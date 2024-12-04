from typing import Tuple
import os
import pandas as pd
from pydantic import BaseModel, Field
from rich import print
from rich.console import Console
from rich.traceback import install

from .llm_invoke import llm_invoke
from .load_prompt_template import load_prompt_template
from .preprocess import preprocess
from .auto_include import auto_include

# Install rich traceback handler
install()
console = Console()

class PromptOutput(BaseModel):
    output_prompt: str = Field(description="The prompt with dependencies inserted")

def insert_includes(
    input_prompt: str,
    directory_path: str,
    csv_filename: str,
    strength: float,
    temperature: float,
) -> Tuple[str, float, str, str]:
    """
    Insert needed dependencies into a prompt.

    Args:
        input_prompt (str): The input prompt to process
        directory_path (str): Directory path where the prompt file is located
        csv_filename (str): Name of the CSV file containing dependencies
        strength (float): Strength parameter for the LLM model
        temperature (float): Temperature parameter for the LLM model

    Returns:
        Tuple[str, float, str, str]: Tuple containing:
            - output_prompt: The prompt with dependencies inserted
            - total_cost: Total cost of running the function
            - model_name: Name of the LLM model used
            - dependencies: Dependencies extracted from the CSV file
    """
    try:
        # Initialize total cost
        total_cost = 0.0
        model_name = ""

        # 1. Load the prompt template
        insert_includes_prompt = load_prompt_template("insert_includes_LLM")
        if not insert_includes_prompt:
            raise ValueError("Failed to load insert_includes_LLM.prompt template")

        # 2. Read or create CSV file
        try:
            if os.path.exists(csv_filename):
                df = pd.read_csv(csv_filename)
                dependencies = df.to_string(index=False)
            else:
                # Create empty CSV if it doesn't exist
                pd.DataFrame(columns=['dependency', 'description']).to_csv(csv_filename, index=False)
                dependencies = ""
        except Exception as e:
            console.print(f"[red]Error reading CSV file: {e}[/red]")
            dependencies = ""

        # 3. Preprocess the prompt template
        processed_prompt = preprocess(insert_includes_prompt, recursive=False, double_curly_brackets=True)

        # 4. Use auto_include to get dependencies
        auto_include_result = auto_include(
            input_prompt=input_prompt,
            directory_path=directory_path,
            csv_file=dependencies,
            strength=strength,
            temperature=temperature,
            verbose=True
        )
        
        if not auto_include_result:
            raise ValueError("auto_include failed to return results")

        auto_output_prompt, _, auto_cost, auto_model = auto_include_result
        total_cost += auto_cost
        model_name = auto_model

        # 5. Run llm_invoke with the processed prompt
        response = llm_invoke(
            prompt=processed_prompt,
            input_json={
                "actual_prompt_to_update": input_prompt,
                "actual_dependencies_to_insert": auto_output_prompt
            },
            strength=strength,
            temperature=temperature,
            output_pydantic=PromptOutput,
            verbose=True
        )

        if not response or 'result' not in response:
            raise ValueError("LLM invocation failed to return results")

        total_cost += response.get('cost', 0.0)
        model_name = response.get('model_name', model_name)
        
        # 6. Return results
        return (
            response['result'].output_prompt,
            total_cost,
            model_name,
            dependencies
        )

    except Exception as e:
        console.print(f"[red]Error in insert_includes: {str(e)}[/red]")
        raise


if __name__ == "__main__":
    from rich import print
    
    def main():
        try:
            output_prompt, total_cost, model_name, dependencies = insert_includes(
                input_prompt="Your prompt here",
                directory_path="path/to/directory",
                csv_filename="dependencies.csv",
                strength=0.7,
                temperature=0.5
            )

            print("[green]Success![/green]")
            print("[blue]Output Prompt:[/blue]")
            print(output_prompt)
            print(f"[blue]Total Cost:[/blue] ${total_cost:.6f}")
            print(f"[blue]Model Used:[/blue] {model_name}")
            print("[blue]Dependencies:[/blue]")
            print(dependencies)

        except Exception as e:
            print(f"[red]Error:[/red] {str(e)}")

    main()