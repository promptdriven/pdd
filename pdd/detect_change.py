from typing import List, Dict, Tuple, Optional
from pathlib import Path
from rich.console import Console
from rich.markdown import Markdown
from pydantic import BaseModel, Field
from . import EXTRACTION_STRENGTH, DEFAULT_STRENGTH, DEFAULT_TIME

from .preprocess import preprocess
from .load_prompt_template import load_prompt_template
from .llm_invoke import llm_invoke

console = Console()

class ChangeInstruction(BaseModel):
    prompt_name: str = Field(description="Name of the prompt file that needs changes")
    change_instructions: str = Field(description="Detailed instructions for the changes needed")

class ChangesList(BaseModel):
    changes_list: List[ChangeInstruction] = Field(description="List of changes to be made")

def detect_change(
    prompt_files: List[str],
    change_description: str,
    strength: float=DEFAULT_STRENGTH,
    temperature: float=0.0,
    time: Optional[float] = DEFAULT_TIME,
    verbose: bool = False
) -> Tuple[List[Dict[str, str]], float, str]:
    """
    Analyze prompt files and determine which ones need changes based on a change description.

    Args:
        prompt_files (List[str]): List of prompt file names to analyze
        change_description (str): Description of the changes to analyze
        strength (float): Strength parameter for the LLM model
        temperature (float): Temperature parameter for the LLM model
        time (float): Time budget for LLM calls.
        verbose (bool): Whether to print detailed information

    Returns:
        Tuple[List[Dict[str, str]], float, str]: Changes list, total cost, and model name
    """
    try:
        # Step 1: Load and preprocess prompt templates
        detect_change_prompt = load_prompt_template("detect_change_LLM")
        if not detect_change_prompt:
            raise ValueError("Failed to load detect_change_LLM prompt template")

        extract_prompt = load_prompt_template("extract_detect_change_LLM")
        if not extract_prompt:
            raise ValueError("Failed to load extract_detect_change_LLM prompt template")

        # Preprocess detect_change prompt
        processed_detect_prompt = preprocess(
            detect_change_prompt,
            recursive=False,
            double_curly_brackets=True,
            exclude_keys=["PROMPT_LIST", "CHANGE_DESCRIPTION"]
        )

        # Step 2: Create prompt list and process change description
        prompt_list = []
        total_cost = 0.0

        for prompt_file in prompt_files:
            try:
                with open(prompt_file, 'r') as f:
                    prompt_content = f.read()
                prompt_list.append({
                    "PROMPT_NAME": Path(prompt_file).name,
                    "PROMPT_DESCRIPTION": prompt_content
                })
            except FileNotFoundError:
                console.print(f"[red]Warning: Could not find prompt file: {prompt_file}[/red]")
                continue

        processed_change_description = preprocess(
            change_description,
            recursive=False,
            double_curly_brackets=False
        )

        # Run initial LLM analysis
        detect_response = llm_invoke(
            prompt=processed_detect_prompt,
            input_json={
                "PROMPT_LIST": prompt_list,
                "CHANGE_DESCRIPTION": processed_change_description
            },
            strength=strength,
            temperature=temperature,
            time=time,
            verbose=verbose
        )

        if verbose:
            console.print("[bold blue]Initial Analysis Results:[/bold blue]")
            console.print(f"Token count: {detect_response.get('token_count', 0)}")
            console.print(f"Cost: ${detect_response.get('cost', 0):.6f}")

        total_cost += detect_response.get('cost', 0)
        model_name = detect_response.get('model_name', '')

        # Step 3: Extract specific changes
        extract_response = llm_invoke(
            prompt=extract_prompt,
            input_json={"llm_output": detect_response['result']},
            strength=EXTRACTION_STRENGTH,
            temperature=0.0,
            time=time,
            verbose=verbose,
            output_pydantic=ChangesList
        )

        total_cost += extract_response.get('cost', 0)

        if verbose:
            console.print("[bold blue]Extraction Results:[/bold blue]")
            console.print(f"Token count: {extract_response.get('token_count', 0)}")
            console.print(f"Cost: ${extract_response.get('cost', 0):.6f}")

        # Step 4: Format and display results
        changes_list = extract_response['result'].changes_list
        if verbose:
            console.print("\n[bold green]Detected Changes:[/bold green]")
            for change in changes_list:
                md = Markdown(f"""
                ### Prompt: {change.prompt_name}
                **Change Instructions:**
                {change.change_instructions}
                """)
                console.print(md)
            console.print(f"\n[bold]Total Cost: ${total_cost:.6f}[/bold]")
            console.print(f"[bold]Model Used: {model_name}[/bold]")

        # Step 5: Return results
        return [
            {
                "prompt_name": change.prompt_name,
                "change_instructions": change.change_instructions
            }
            for change in changes_list
        ], total_cost, model_name

    except Exception as e:
        console.print(f"[red]Error in detect_change: {str(e)}[/red]")
        raise