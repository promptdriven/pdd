"""
This module provides the `auto_include` function to automatically find and
insert dependencies into a prompt.
"""
from io import StringIO
from typing import Tuple, Optional

import pandas as pd
from pydantic import BaseModel, Field
from rich.console import Console
from rich.panel import Panel

from . import DEFAULT_TIME, DEFAULT_STRENGTH
from .llm_invoke import llm_invoke
from .load_prompt_template import load_prompt_template
from .summarize_directory import summarize_directory

console = Console()

class AutoIncludeOutput(BaseModel):
    """
    Pydantic model for the output of the auto_include extraction.
    """
    string_of_includes: str = Field(description="The string of includes to be added to the prompt")


def _validate_input(input_prompt: str, directory_path: str, strength: float, temperature: float):
    """Validate the inputs for the auto_include function."""
    if not input_prompt:
        raise ValueError("Input prompt cannot be empty")
    if not directory_path:
        raise ValueError("Invalid 'directory_path'.")
    if not 0 <= strength <= 1:
        raise ValueError("Strength must be between 0 and 1")
    if not 0 <= temperature <= 1:
        raise ValueError("Temperature must be between 0 and 1")


def _get_available_includes_from_csv(csv_output: str) -> list[str]:
    """Parse the CSV output and return a list of available includes."""
    if not csv_output:
        return []
    try:
        # pylint: disable=invalid-name
        dataframe = pd.read_csv(StringIO(csv_output))
        return dataframe.apply(
            lambda row: f"File: {row['full_path']}\nSummary: {row['file_summary']}",
            axis=1
        ).tolist()
    except Exception as ex:
        console.print(f"[red]Error parsing CSV: {str(ex)}[/red]")
        return []


def _load_prompts() -> tuple[str, str]:
    """Load the prompt templates."""
    auto_include_prompt = load_prompt_template("auto_include_LLM")
    extract_prompt = load_prompt_template("extract_auto_include_LLM")
    if not auto_include_prompt or not extract_prompt:
        raise ValueError("Failed to load prompt templates")
    return auto_include_prompt, extract_prompt


def _summarize(directory_path: str, csv_file: Optional[str], llm_kwargs: dict) -> tuple[str, float, str]:
    """Summarize the directory."""
    return summarize_directory(
        directory_path=directory_path,
        csv_file=csv_file,
        **llm_kwargs
    )


def _run_llm_and_extract(
    auto_include_prompt: str,
    extract_prompt: str,
    input_prompt: str,
    available_includes: list[str],
    llm_kwargs: dict,
) -> tuple[str, float, str]:
    """Run the LLM prompts and extract the dependencies."""
    # pylint: disable=broad-except
    # Run auto_include_LLM prompt
    auto_include_response = llm_invoke(
        prompt=auto_include_prompt,
        input_json={
            "input_prompt": input_prompt,
            "available_includes": "\n".join(available_includes)
        },
        **llm_kwargs
    )
    total_cost = auto_include_response["cost"]
    model_name = auto_include_response["model_name"]

    # Run extract_auto_include_LLM prompt
    try:
        extract_response = llm_invoke(
            prompt=extract_prompt,
            input_json={"llm_output": auto_include_response["result"]},
            output_pydantic=AutoIncludeOutput,
            **llm_kwargs
        )
        total_cost += extract_response["cost"]
        model_name = extract_response["model_name"]
        dependencies = extract_response["result"].string_of_includes
    except Exception as ex:
        console.print(f"[red]Error extracting dependencies: {str(ex)}[/red]")
        dependencies = ""
    return dependencies, total_cost, model_name


def auto_include(
    input_prompt: str,
    directory_path: str,
    csv_file: Optional[str] = None,
    strength: float = DEFAULT_STRENGTH,
    temperature: float = 0.0,
    time: float = DEFAULT_TIME,
    verbose: bool = False
) -> Tuple[str, str, float, str]:
    """
    Automatically find and insert proper dependencies into the prompt.

    Args:
        input_prompt (str): The prompt requiring includes
        directory_path (str): Directory path of dependencies
        csv_file (Optional[str]): Contents of existing CSV file
        strength (float): Strength of LLM model (0-1)
        temperature (float): Temperature of LLM model (0-1)
        time (float): Time budget for LLM calls
        verbose (bool): Whether to print detailed information

    Returns:
        Tuple[str, str, float, str]: (dependencies, csv_output, total_cost, model_name)
    """
    # pylint: disable=broad-except
    try:
        _validate_input(input_prompt, directory_path, strength, temperature)
        
        llm_kwargs = {
            "strength": strength,
            "temperature": temperature,
            "time": time,
            "verbose": verbose
        }

        if verbose:
            console.print(Panel("Step 1: Loading prompt templates", style="blue"))

        auto_include_prompt, extract_prompt = _load_prompts()
        
        if verbose:
            console.print(Panel("Step 2: Running summarize_directory", style="blue"))

        csv_output, summary_cost, summary_model = _summarize(
            directory_path, csv_file, llm_kwargs
        )

        available_includes = _get_available_includes_from_csv(csv_output)
        
        if verbose:
            console.print(Panel("Step 3: Running auto_include_LLM prompt", style="blue"))

        dependencies, llm_cost, llm_model_name = _run_llm_and_extract(
            auto_include_prompt=auto_include_prompt,
            extract_prompt=extract_prompt,
            input_prompt=input_prompt,
            available_includes=available_includes,
            llm_kwargs=llm_kwargs,
        )
        
        total_cost = summary_cost + llm_cost
        model_name = llm_model_name or summary_model

        if verbose:
            console.print(Panel(
                (
                    f"Results:\n"
                    f"Dependencies: {dependencies}\n"
                    f"CSV Output: {csv_output}\n"
                    f"Total Cost: ${total_cost:.6f}\n"
                    f"Model Used: {model_name}"
                ),
                style="green"
            ))

        return dependencies, csv_output, total_cost, model_name

    except Exception as ex:
        console.print(f"[red]Error in auto_include: {str(ex)}[/red]")
        raise


def main():
    """Example usage of auto_include function"""
    try:
        # Example inputs
        input_prompt = "Write a function to process image data"
        directory_path = "context/c*.py"
        csv_file = (
            "full_path,file_summary,date\n"
            "context/image_utils.py,"
            "\"Image processing utilities\",2023-01-01T10:00:00"
        )

        dependencies, _, total_cost, model_name = auto_include(
            input_prompt=input_prompt,
            directory_path=directory_path,
            csv_file=csv_file,
            strength=0.7,
            temperature=0.0,
            time=DEFAULT_TIME,
            verbose=True
        )

        console.print("\n[blue]Final Results:[/blue]")
        console.print(f"Dependencies: {dependencies}")
        console.print(f"Total Cost: ${total_cost:.6f}")
        console.print(f"Model Used: {model_name}")

    except Exception as ex:
        console.print(f"[red]Error in main: {str(ex)}[/red]")

if __name__ == "__main__":
    main()