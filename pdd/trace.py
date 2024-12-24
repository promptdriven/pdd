from typing import Tuple, Optional
from rich import print
from rich.console import Console
from pydantic import BaseModel, Field
import difflib
from .load_prompt_template import load_prompt_template
from .preprocess import preprocess
from .llm_invoke import llm_invoke

console = Console()

class PromptLineOutput(BaseModel):
    prompt_line: str = Field(description="The line from the prompt file that matches the code")

def trace(
    code_file: str,
    code_line: int,
    prompt_file: str,
    strength: float = 0.5,
    temperature: float = 0,
    verbose: bool = False
) -> Tuple[Optional[int], float, str]:
    """
    Trace a line of code back to its corresponding line in the prompt file.

    Args:
        code_file (str): Content of the code file
        code_line (int): Line number in the code file
        prompt_file (str): Content of the prompt file
        strength (float, optional): Model strength. Defaults to 0.5
        temperature (float, optional): Model temperature. Defaults to 0
        verbose (bool, optional): Whether to print detailed information. Defaults to False

    Returns:
        Tuple[Optional[int], float, str]: (prompt line number, total cost, model name)
    """
    try:
        # Input validation
        if not all([code_file, prompt_file]) or not isinstance(code_line, int):
            raise ValueError("Invalid input parameters")

        total_cost = 0
        model_name = ""

        # Step 1: Extract the code line string
        code_lines = code_file.splitlines()
        if code_line < 1 or code_line > len(code_lines):
            raise ValueError(f"Code line number {code_line} is out of range")
        code_str = code_lines[code_line - 1]

        # Step 2 & 3: Load and preprocess trace_LLM prompt
        trace_prompt = load_prompt_template("trace_LLM")
        if not trace_prompt:
            raise ValueError("Failed to load trace_LLM prompt template")
        trace_prompt = preprocess(trace_prompt, recursive=False, double_curly_brackets=False)

        # Step 4: First LLM invocation
        if verbose:
            console.print("[bold blue]Running trace analysis...[/bold blue]")

        trace_response = llm_invoke(
            prompt=trace_prompt,
            input_json={
                "CODE_FILE": code_file,
                "CODE_STR": code_str,
                "PROMPT_FILE": prompt_file
            },
            strength=strength,
            temperature=temperature,
            verbose=verbose
        )

        total_cost += trace_response['cost']
        model_name = trace_response['model_name']

        # Step 5: Load and preprocess extract_promptline_LLM prompt
        extract_prompt = load_prompt_template("extract_promptline_LLM")
        if not extract_prompt:
            raise ValueError("Failed to load extract_promptline_LLM prompt template")
        extract_prompt = preprocess(extract_prompt, recursive=False, double_curly_brackets=False)

        # Step 6: Second LLM invocation
        if verbose:
            console.print("[bold blue]Extracting prompt line...[/bold blue]")

        extract_response = llm_invoke(
            prompt=extract_prompt,
            input_json={"llm_output": trace_response['result']},
            strength=strength,
            temperature=temperature,
            verbose=verbose,
            output_pydantic=PromptLineOutput
        )

        total_cost += extract_response['cost']
        prompt_line_str = extract_response['result'].prompt_line

        # Step 7: Find matching line in prompt file using fuzzy matching
        prompt_lines = prompt_file.splitlines()
        best_match = None
        highest_ratio = 0

        if verbose:
            console.print(f"Searching for line: {prompt_line_str}")

        normalized_search = prompt_line_str.strip()

        for i, line in enumerate(prompt_lines, 1):
            normalized_line = line.strip()
            ratio = difflib.SequenceMatcher(None, normalized_search, normalized_line).ratio()

            if verbose:
                console.print(f"Line {i}: '{line}' - Match ratio: {ratio}")

            # Increase threshold to 0.9 for more precise matching
            if ratio > highest_ratio and ratio > 0.9:
                # Additional check for exact content match after normalization
                if normalized_search == normalized_line:
                    highest_ratio = ratio
                    best_match = i
                    break  # Exit on exact match
                highest_ratio = ratio
                best_match = i

        # Step 8: Return results
        if verbose:
            console.print(f"[green]Found matching line: {best_match}[/green]")
            console.print(f"[green]Total cost: ${total_cost:.6f}[/green]")
            console.print(f"[green]Model used: {model_name}[/green]")

        return best_match, total_cost, model_name

    except Exception as e:
        console.print(f"[bold red]Error in trace function: {str(e)}[/bold red]")
        return None, 0.0, ""