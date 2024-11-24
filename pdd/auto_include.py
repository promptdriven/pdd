from typing import Tuple, Optional
from pydantic import BaseModel, Field
from rich import print
from rich.console import Console
from rich.panel import Panel
from .load_prompt_template import load_prompt_template
from .llm_invoke import llm_invoke
from .summarize_directory import summarize_directory
import csv
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
        directory_path (str): Directory path pattern for dependencies
        csv_file (Optional[str]): Existing CSV content
        strength (float): Model strength (0-1)
        temperature (float): Model temperature (0-1)
        verbose (bool): Whether to print detailed output

    Returns:
        Tuple[str, str, float, str]: (output_prompt, csv_output, total_cost, model_name)
    """
    try:
        # Input validation
        if not input_prompt or not directory_path:
            raise ValueError("Input prompt and directory path are required")
        if not (0 <= strength <= 1) or not (0 <= temperature <= 1):
            raise ValueError("Strength and temperature must be between 0 and 1")

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
            console.print(Panel("Step 2: Summarizing directory", style="blue"))

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

        # Parse CSV to create available_includes
        available_includes = []
        csv_reader = csv.DictReader(StringIO(csv_output))
        for row in csv_reader:
            available_includes.append(f"{row['full_path']}: {row['file_summary']}")

        if verbose:
            console.print(Panel("Step 3: Running auto_include_LLM", style="blue"))

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
            console.print(Panel("Step 4: Running extract_auto_include_LLM", style="blue"))

        # Run extract_auto_include_LLM prompt
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
            console.print(Panel("Step 5: Generating output prompt", style="blue"))

        # Create output prompt
        string_of_includes = extract_response["result"].string_of_includes
        output_prompt = f"{string_of_includes}\n\n{input_prompt}"

        if verbose:
            console.print(Panel(f"Total cost: ${total_cost:.6f}", style="green"))
            console.print(Panel(f"Model used: {model_name}", style="green"))

        return output_prompt, csv_output, total_cost, model_name

    except Exception as e:
        console.print(Panel(f"[red]Error: {str(e)}", style="red"))
        raise

if __name__ == "__main__":
    def main():
        try:
            # Example usage
            input_prompt = "Write a function that sorts a list"
            directory_path = "context/c*.py"
            csv_file = """full_path,file_summary,date
context/example1.py,"Contains sorting algorithms",2023-01-01"""

            output_prompt, csv_output, total_cost, model_name = auto_include(
                input_prompt=input_prompt,
                directory_path=directory_path,
                csv_file=csv_file,
                strength=0.7,
                temperature=0.0,
                verbose=True
            )

            print("\nResults:")
            print(f"Output Prompt:\n{output_prompt}")
            print(f"CSV Output:\n{csv_output}")
            print(f"Total Cost: ${total_cost:.6f}")
            print(f"Model Used: {model_name}")

        except Exception as e:
            console.print(f"[red]Error in main: {str(e)}[/red]")

    main()