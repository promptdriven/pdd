from typing import Tuple, Optional
from rich import print as rprint
from rich.markdown import Markdown
from pydantic import BaseModel, Field
from .load_prompt_template import load_prompt_template
from .preprocess import preprocess
from .llm_invoke import llm_invoke

from . import EXTRACTION_STRENGTH, DEFAULT_STRENGTH, DEFAULT_TEMPERATURE, DEFAULT_TIME

class PromptSplit(BaseModel):
    extracted_functionality: str = Field(description="The extracted functionality as a sub-module prompt")
    remaining_prompt: str = Field(description="The modified original prompt that will import the extracted functionality")

def split(
    input_prompt: str,
    input_code: str,
    example_code: str,
    strength: float = DEFAULT_STRENGTH,
    temperature: float = DEFAULT_TEMPERATURE,
    time: Optional[float] = DEFAULT_TIME,
    verbose: bool = False
) -> Tuple[Tuple[str, str], float, str]:
    """
    Split a prompt into extracted functionality and remaining prompt.

    Args:
        input_prompt (str): The prompt to split.
        input_code (str): The code generated from the input_prompt.
        example_code (str): Example code showing usage.
        strength (float): LLM strength parameter (0-1).
        temperature (float): LLM temperature parameter (0-1).
        time (Optional[float]): Time allocation for the LLM.
        verbose (bool): Whether to print detailed information.

    Returns:
        Tuple[Tuple[str, str], float, str]: 
            ((extracted_functionality, remaining_prompt), total_cost, model_name)
            where model_name is the name of the model used (returned as the second to last tuple element)
            and total_cost is the aggregated cost from all LLM invocations.
    """
    total_cost = 0.0
    model_name = ""


    # Input validation
    if not all([input_prompt, input_code, example_code]):
        raise ValueError("All input parameters (input_prompt, input_code, example_code) must be provided")
    
    if not 0 <= strength <= 1 or not 0 <= temperature <= 1:
        raise ValueError("Strength and temperature must be between 0 and 1")

    try:
        # 1. Load prompt templates
        split_prompt = load_prompt_template("split_LLM")
        extract_prompt = load_prompt_template("extract_prompt_split_LLM")
        
        if not split_prompt or not extract_prompt:
            raise ValueError("Failed to load prompt templates")

        # 2. Preprocess prompts
        processed_split_prompt = preprocess(
            split_prompt,
            recursive=False,
            double_curly_brackets=True,
            exclude_keys=['input_prompt', 'input_code', 'example_code']
        )
        
        processed_extract_prompt = preprocess(
            extract_prompt,
            recursive=False,
            double_curly_brackets=False
        )

        # 3. First LLM invocation
        if verbose:
            rprint("[bold blue]Running initial prompt split...[/bold blue]")

        split_response = llm_invoke(
            prompt=processed_split_prompt,
            input_json={
                "input_prompt": input_prompt,
                "input_code": input_code,
                "example_code": example_code
            },
            strength=strength,
            temperature=temperature,
            time=time,
            verbose=verbose
        )
        total_cost += split_response["cost"]
        # Capture the model name from the first invocation.
        model_name = split_response["model_name"]

        # 4. Extract JSON with second LLM invocation
        if verbose:
            rprint("[bold blue]Extracting split prompts...[/bold blue]")

        extract_response = llm_invoke(
            prompt=processed_extract_prompt,
            input_json={"llm_output": split_response["result"]},
            strength=EXTRACTION_STRENGTH,  # Fixed strength for extraction
            temperature=temperature,
            output_pydantic=PromptSplit,
            verbose=verbose,
            time=time  # Pass time to the second llm_invoke call
        )
        total_cost += extract_response["cost"]

        # Extract results
        result: PromptSplit = extract_response["result"]
        extracted_functionality = result.extracted_functionality
        remaining_prompt = result.remaining_prompt

        # 5. Print verbose output if requested
        if verbose:
            rprint("\n[bold green]Final Results:[/bold green]")
            rprint(Markdown(f"### Extracted Functionality\n{extracted_functionality}"))
            rprint(Markdown(f"### Remaining Prompt\n{remaining_prompt}"))
            rprint(f"[bold cyan]Total Cost: ${total_cost:.6f}[/bold cyan]")
            rprint(f"[bold cyan]Model used: {model_name}[/bold cyan]")

        # 6. Return results with standardized order: (result_data, cost, model_name)
        return (extracted_functionality, remaining_prompt), total_cost, model_name

    except Exception as e:
        # Print an error message, then raise an exception that includes
        # the prefix "Error in split function: …" in its final message.
        rprint(f"[bold red]Error in split function: {str(e)}[/bold red]")
        # Re-raise using the same exception type but with a modified message.
        raise type(e)(f"Error in split function: {str(e)}") from e