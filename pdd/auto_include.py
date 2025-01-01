from typing import Tuple, Optional
from pydantic import BaseModel, Field
from rich import print
from rich.console import Console
from rich.panel import Panel
from .load_prompt_template import load_prompt_template
from .llm_invoke import llm_invoke
from .summarize_directory import summarize_directory
import pandas as pd
from io import StringIO

console = Console()

class AutoIncludeOutput(BaseModel):
    string_of_includes: str = Field(description="The string of includes to be added to the prompt")

def auto_include(
    input_prompt: str,
    directory_path: str,
    csv_file: Optional[str] = None,
    strength: float = 0.7,
    temperature: float = 0.0,
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
        verbose (bool): Whether to print detailed information

    Returns:
        Tuple[str, str, float, str]: (dependencies, csv_output, total_cost, model_name)
    """
    try:
        # Input validation
        if not input_prompt:
            raise ValueError("Input prompt cannot be empty")
        if not directory_path:
            raise ValueError("Invalid 'directory_path'.")
        if not 0 <= strength <= 1:
            raise ValueError("Strength must be between 0 and 1")
        if not 0 <= temperature <= 1:
            raise ValueError("Temperature must be between 0 and 1")

        total_cost = 0.0
        model_name = ""

        if verbose:
            console.print(Panel("Step 1: Loading prompt templates", style="blue"))

        # Load prompt templates
        auto_include_prompt = load_prompt_template("auto_include_LLM")
        extract_prompt = load_prompt_template("extract_auto_include_LLM")

        if not auto_include_prompt or not extract_prompt:
            raise ValueError("Failed to load prompt templates")

        if verbose:
            console.print(Panel("Step 2: Running summarize_directory", style="blue"))

        # Run summarize_directory
        csv_output, summary_cost, summary_model = summarize_directory(
            directory_path=directory_path,
            strength=strength,
            temperature=temperature,
            verbose=verbose,
            csv_file=csv_file
        )
        total_cost += summary_cost
        model_name = summary_model

        # Parse CSV to get available includes
        if not csv_output:
            available_includes = []
        else:
            try:
                df = pd.read_csv(StringIO(csv_output))
                available_includes = df.apply(
                    lambda row: f"File: {row['full_path']}\nSummary: {row['file_summary']}",
                    axis=1
                ).tolist()
            except Exception as e:
                console.print(f"[red]Error parsing CSV: {str(e)}[/red]")
                available_includes = []

        if verbose:
            console.print(Panel("Step 3: Running auto_include_LLM prompt", style="blue"))

        # Run auto_include_LLM prompt
        auto_include_response = llm_invoke(
            prompt=auto_include_prompt,
            input_json={
                "input_prompt": input_prompt,
                "available_includes": "\n".join(available_includes)
            },
            strength=strength,
            temperature=temperature,
            verbose=verbose
        )
        total_cost += auto_include_response["cost"]
        model_name = auto_include_response["model_name"]

        if verbose:
            console.print(Panel("Step 4: Running extract_auto_include_LLM prompt", style="blue"))

        # Run extract_auto_include_LLM prompt
        try:
            extract_response = llm_invoke(
                prompt=extract_prompt,
                input_json={"llm_output": auto_include_response["result"]},
                strength=strength,
                temperature=temperature,
                verbose=verbose,
                output_pydantic=AutoIncludeOutput
            )
            total_cost += extract_response["cost"]
            model_name = extract_response["model_name"]

            if verbose:
                console.print(Panel("Step 5: Extracting dependencies", style="blue"))

            # Extract dependencies
            dependencies = extract_response["result"].string_of_includes
        except Exception as e:
            console.print(f"[red]Error extracting dependencies: {str(e)}[/red]")
            dependencies = ""

        if verbose:
            console.print(Panel(f"""
Results:
Dependencies: {dependencies}
CSV Output: {csv_output}
Total Cost: ${total_cost:.6f}
Model Used: {model_name}
            """, style="green"))

        return dependencies, csv_output, total_cost, model_name

    except Exception as e:
        console.print(f"[red]Error in auto_include: {str(e)}[/red]")
        raise

def main():
    """Example usage of auto_include function"""
    try:
        # Example inputs
        input_prompt = "Write a function to process image data"
        directory_path = "context/c*.py"
        csv_file = """full_path,file_summary,date
context/image_utils.py,"Image processing utilities",2023-01-01T10:00:00"""

        dependencies, csv_output, total_cost, model_name = auto_include(
            input_prompt=input_prompt,
            directory_path=directory_path,
            csv_file=csv_file,
            strength=0.7,
            temperature=0.0,
            verbose=True
        )

        console.print("\n[blue]Final Results:[/blue]")
        console.print(f"Dependencies: {dependencies}")
        console.print(f"Total Cost: ${total_cost:.6f}")
        console.print(f"Model Used: {model_name}")

    except Exception as e:
        console.print(f"[red]Error in main: {str(e)}[/red]")

if __name__ == "__main__":
    main()