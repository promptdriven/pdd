from typing import Tuple
from pathlib import Path
import pandas as pd
from rich import print
from rich.console import Console
from pydantic import BaseModel, Field

from .llm_invoke import llm_invoke
from .load_prompt_template import load_prompt_template
from .preprocess import preprocess
from .auto_include import auto_include

console = Console()

class InsertIncludesOutput(BaseModel):
    output_prompt: str = Field(description="The prompt with dependencies inserted")

def insert_includes(
    input_prompt: str,
    directory_path: str,
    csv_filename: str,
    strength: float = 0.7,
    temperature: float = 0.5,
) -> Tuple[str, float, str, str]:
    """
    Determine needed dependencies and insert them into a prompt.

    Args:
        input_prompt (str): The input prompt to process
        directory_path (str): Directory path where the prompt file is located
        csv_filename (str): Name of the CSV file containing dependencies
        strength (float, optional): Strength parameter for LLM. Defaults to 0.7
        temperature (float, optional): Temperature parameter for LLM. Defaults to 0.5

    Returns:
        Tuple[str, float, str, str]: Tuple containing:
            - output_prompt: The prompt with dependencies inserted
            - total_cost: Total cost of running the function
            - model_name: Name of the LLM model used
            - dependencies: Dependencies extracted from CSV file

    Raises:
        FileNotFoundError: If required files cannot be found
        ValueError: If input parameters are invalid
        Exception: For other unexpected errors
    """
    try:
        # Validate inputs
        if not input_prompt:
            raise ValueError("Input prompt cannot be empty")
        if not directory_path:
            raise ValueError("Directory path cannot be empty")
        if not csv_filename:
            raise ValueError("CSV filename cannot be empty")
        if not (0 <= strength <= 1):
            raise ValueError("Strength must be between 0 and 1")
        if not (0 <= temperature <= 1):
            raise ValueError("Temperature must be between 0 and 1")

        total_cost = 0.0
        current_model = ""

        # 1. Load the insert_includes prompt template
        insert_includes_prompt = load_prompt_template("insert_includes_LLM")
        if not insert_includes_prompt:
            raise FileNotFoundError("Could not load insert_includes_LLM.prompt")

        # 2. Preprocess the prompt template
        processed_prompt = preprocess(insert_includes_prompt, recursive=False, double_curly_brackets=True)

        # 3. Get dependencies using auto_include
        try:
            # Read existing CSV file if it exists
            csv_content = ""
            csv_path = Path(csv_filename)
            if csv_path.exists():
                with open(csv_path, 'r') as file:
                    csv_content = file.read()

            output_prompt, csv_output, cost, model = auto_include(
                input_prompt=input_prompt,
                directory_path=directory_path,
                csv_file=csv_content,
                strength=strength,
                temperature=temperature,
                verbose=False
            )
            total_cost += cost
            current_model = model
            dependencies = csv_output

        except Exception as e:
            console.print(f"[red]Error in auto_include: {str(e)}[/red]")
            raise

        # 4. Run llm_invoke with the processed prompt
        try:
            response = llm_invoke(
                prompt=processed_prompt,
                input_json={
                    "actual_prompt_to_update": input_prompt,
                    "actual_dependencies_to_insert": dependencies
                },
                strength=strength,
                temperature=temperature,
                output_pydantic=InsertIncludesOutput,
                verbose=False
            )
            total_cost += response['cost']
            current_model = response['model_name']
            final_output = response['result'].output_prompt

        except Exception as e:
            console.print(f"[red]Error in llm_invoke: {str(e)}[/red]")
            raise

        # 5. Return results
        return final_output, total_cost, current_model, dependencies

    except Exception as e:
        console.print(f"[red]Error in insert_includes: {str(e)}[/red]")
        raise

def main():
    """Example usage of the insert_includes function."""
    try:
        # Example parameters
        input_prompt = "Write a function to sort a list"
        directory_path = "./context"
        csv_filename = "dependencies.csv"
        
        output_prompt, total_cost, model_name, dependencies = insert_includes(
            input_prompt=input_prompt,
            directory_path=directory_path,
            csv_filename=csv_filename
        )

        # Pretty print results
        console.print("\n[bold green]Results:[/bold green]")
        console.print("[bold blue]Output Prompt:[/bold blue]")
        console.print(output_prompt)
        console.print(f"\n[bold blue]Total Cost:[/bold blue] ${total_cost:.6f}")
        console.print(f"[bold blue]Model Used:[/bold blue] {model_name}")
        console.print("[bold blue]Dependencies:[/bold blue]")
        console.print(dependencies)

    except Exception as e:
        console.print(f"[red]Error in main: {str(e)}[/red]")

if __name__ == "__main__":
    main()