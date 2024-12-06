from typing import Tuple
from pathlib import Path
from pydantic import BaseModel, Field
from rich import print
from rich.console import Console
from rich.markdown import Markdown

from .llm_invoke import llm_invoke
from .load_prompt_template import load_prompt_template
from .preprocess import preprocess
from .auto_include import auto_include

console = Console()

class PromptOutput(BaseModel):
    output_prompt: str = Field(description="The prompt with dependencies inserted")

def insert_includes(
    input_prompt: str,
    directory_path: str,
    csv_filename: str,
    strength: float,
    temperature: float,
) -> Tuple[str, str, float, str]:
    """
    Determine needed dependencies and insert them into a prompt.

    Args:
        input_prompt (str): The prompt to process
        directory_path (str): Directory path where the prompt file is located
        csv_filename (str): Name of the CSV file containing dependencies
        strength (float): Strength parameter for the LLM model
        temperature (float): Temperature parameter for the LLM model

    Returns:
        Tuple[str, str, float, str]: Tuple containing:
            - output_prompt: The prompt with dependencies inserted
            - dependencies: Updated dependencies from auto_include
            - total_cost: Total cost of running the function
            - model_name: Name of the LLM model used
    """
    try:
        # Step 1: Load the prompt template
        insert_includes_prompt = load_prompt_template("insert_includes_LLM")
        if not insert_includes_prompt:
            raise ValueError("Failed to load insert_includes_LLM.prompt template")

        # Step 2: Read the CSV file
        try:
            with open(csv_filename, 'r') as file:
                csv_content = file.read()
        except FileNotFoundError:
            console.print(f"[yellow]Warning: CSV file '{csv_filename}' not found. Creating empty CSV.[/yellow]")
            csv_content = "full_path,file_summary,date\n"
            with open(csv_filename, 'w') as file:
                file.write(csv_content)

        # Step 3: Preprocess the prompt template
        processed_template = preprocess(insert_includes_prompt, recursive=False, double_curly_brackets=True)

        # Step 4: Use auto_include to get dependencies
        dependencies, csv_output, auto_include_cost, auto_include_model = auto_include(
            input_prompt=input_prompt,
            directory_path=directory_path,
            csv_file=csv_content,
            strength=strength,
            temperature=temperature,
            verbose=True
        )

        # Step 5: Run llm_invoke with the processed template
        response = llm_invoke(
            prompt=processed_template,
            input_json={
                "actual_prompt_to_update": input_prompt,
                "actual_dependencies_to_insert": dependencies
            },
            strength=strength,
            temperature=temperature,
            verbose=True,
            output_pydantic=PromptOutput
        )

        # Extract results
        result: PromptOutput = response['result']
        total_cost = auto_include_cost + response['cost']
        model_name = response['model_name']

        # Pretty print the results
        console.print("\n[bold green]Dependencies successfully inserted![/bold green]")
        console.print(f"[blue]Model used: {model_name}[/blue]")
        console.print(f"[blue]Total cost: ${total_cost:.6f}[/blue]")

        # Return the results
        return (
            result.output_prompt,
            dependencies,
            total_cost,
            model_name
        )

    except Exception as e:
        console.print(f"[bold red]Error in insert_includes:[/bold red] {str(e)}")
        raise

def main():
    """Example usage of the insert_includes function."""
    # Example inputs
    input_prompt = """% Generate a Python function that calculates fibonacci numbers.
    
    <include>context/math_utils.py</include>
    """
    directory_path = "context/*.py"
    csv_filename = "dependencies.csv"
    strength = 0.7
    temperature = 0.5

    try:
        output_prompt, dependencies, total_cost, model_name = insert_includes(
            input_prompt=input_prompt,
            directory_path=directory_path,
            csv_filename=csv_filename,
            strength=strength,
            temperature=temperature
        )

        console.print("\n[bold]Results:[/bold]")
        console.print(Markdown(f"### Output Prompt\n```\n{output_prompt}\n```"))
        console.print(Markdown(f"### Dependencies\n```\n{dependencies}\n```"))
        console.print(f"Total Cost: ${total_cost:.6f}")
        console.print(f"Model Used: {model_name}")

    except Exception as e:
        console.print(f"[bold red]Error in main:[/bold red] {str(e)}")

if __name__ == "__main__":
    main()