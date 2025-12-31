from typing import Tuple, Optional
from rich import print
from rich.markdown import Markdown
from rich.console import Console
from . import EXTRACTION_STRENGTH, DEFAULT_STRENGTH, DEFAULT_TIME
from .load_prompt_template import load_prompt_template
from .preprocess import preprocess
from .llm_invoke import llm_invoke
from .unfinished_prompt import unfinished_prompt
from .continue_generation import continue_generation
from .postprocess import postprocess

console = Console()

def generate_test(
    prompt: str,
    code: str,
    strength: float = DEFAULT_STRENGTH,
    temperature: float = 0.0,
    time: float = DEFAULT_TIME,
    language: str = "python",
    verbose: bool = False,
    source_file_path: Optional[str] = None,
    test_file_path: Optional[str] = None,
    module_name: Optional[str] = None,
    existing_tests: Optional[str] = None
) -> Tuple[str, float, str]:
    """
    Generate a unit test from a code file using LLM.

    Args:
        prompt (str): The prompt that generated the code file.
        code (str): The code to generate a unit test from.
        strength (float): The strength of the LLM model (0-1).
        temperature (float): The temperature of the LLM model.
        language (str): The programming language for the unit test.
        time (float, optional): Time budget for LLM calls. Defaults to DEFAULT_TIME.
        verbose (bool): Whether to print detailed information.
        source_file_path (Optional[str]): Absolute or relative path to the code under test.
        test_file_path (Optional[str]): Destination path for the generated test file.
        module_name (Optional[str]): Module name (without extension) for proper imports.
        existing_tests (Optional[str]): Content of existing tests to append to (for merge mode).

    Returns:
        Tuple[str, float, str]: (unit_test, total_cost, model_name)
    """
    total_cost = 0.0
    model_name = ""

    try:
        # Step 1: Load prompt template
        template = load_prompt_template("generate_test_LLM")
        if not template:
            raise ValueError("Failed to load generate_test_LLM prompt template")

        # Step 2: Preprocess template
        processed_template = preprocess(template, recursive=False, double_curly_brackets=False)
        processed_prompt = preprocess(prompt, recursive=False, double_curly_brackets=False)

        # Step 3: Run through LLM
        input_json = {
            "prompt_that_generated_code": processed_prompt,
            "code": code,
            "language": language,
            "source_file_path": source_file_path or "",
            "test_file_path": test_file_path or "",
            "module_name": module_name or "",
            "existing_tests": existing_tests or "",
        }

        if verbose:
            console.print("[bold blue]Generating unit test...[/bold blue]")

        response = llm_invoke(
            prompt=processed_template,
            input_json=input_json,
            strength=strength,
            temperature=temperature,
            time=time,
            verbose=verbose
        )

        total_cost += response['cost']
        model_name = response['model_name']
        result = response['result']

        # Validate that we got a non-empty result
        if not result or not result.strip():
            raise ValueError(f"LLM test generation returned empty result. Model: {model_name}, Cost: ${response['cost']:.6f}")

        if verbose:
            console.print(Markdown(result))
            console.print(f"[bold green]Initial generation cost: ${total_cost:.6f}[/bold green]")

        # Step 4: Check if generation is complete
        last_600_chars = result[-600:] if len(result) > 600 else result
        
        # Validate that the last_600_chars is not empty after stripping
        if not last_600_chars.strip():
            # If the tail is empty, assume generation is complete
            if verbose:
                console.print("[bold yellow]Last 600 chars are empty, assuming generation is complete[/bold yellow]")
            reasoning = "Generation appears complete (tail is empty)"
            is_finished = True
            check_cost = 0.0
            check_model = model_name
        else:
            reasoning, is_finished, check_cost, check_model = unfinished_prompt(
                prompt_text=last_600_chars,
                strength=strength,
                temperature=temperature,
                time=time,
                language=language,
                verbose=verbose
            )
        total_cost += check_cost

        if not is_finished:
            if verbose:
                console.print("[bold yellow]Generation incomplete. Continuing...[/bold yellow]")
            
            continued_result, continue_cost, continue_model = continue_generation(
                formatted_input_prompt=processed_template,
                llm_output=result,
                strength=strength,
                temperature=temperature,
                time=time,
                language=language,
                verbose=verbose
            )
            total_cost += continue_cost
            result = continued_result
            model_name = continue_model

        # Process the final result
        try:
            processed_result, post_cost, post_model = postprocess(
                result,
                language=language,
                strength=EXTRACTION_STRENGTH,
                temperature=temperature,
                time=time,
                verbose=verbose
            )
            total_cost += post_cost
        except Exception as e:
            console.print(f"[bold red]Postprocess failed: {str(e)}[/bold red]")
            console.print(f"[bold yellow]Falling back to raw result[/bold yellow]")
            
            # Try to extract code blocks directly from the raw result
            import re
            code_blocks = re.findall(r'```(?:python)?\s*(.*?)```', result, re.DOTALL | re.IGNORECASE)
            
            if code_blocks:
                # Use the first substantial code block
                for block in code_blocks:
                    if len(block.strip()) > 100 and ('def test_' in block or 'import' in block):
                        processed_result = block.strip()
                        break
                else:
                    processed_result = code_blocks[0].strip() if code_blocks else result
            else:
                # No code blocks found, use raw result
                processed_result = result
            
            post_cost = 0.0

        # Step 5: Print total cost if verbose
        if verbose:
            console.print(f"[bold green]Total cost: ${total_cost:.6f}[/bold green]")
            console.print(f"[bold blue]Final model used: {model_name}[/bold blue]")

        # Step 6: Return results
        return processed_result, total_cost, model_name

    except Exception as e:
        console.print(f"[bold red]Error: {str(e)}[/bold red]")
        raise


def _validate_inputs(
    prompt: str,
    code: str,
    strength: float,
    temperature: float,
    language: str
) -> None:
    """Validate input parameters."""
    if not prompt or not isinstance(prompt, str):
        raise ValueError("Prompt must be a non-empty string")
    if not code or not isinstance(code, str):
        raise ValueError("Code must be a non-empty string")
    if not isinstance(strength, float) or not 0 <= strength <= 1:
        raise ValueError("Strength must be a float between 0 and 1")
    if not isinstance(temperature, float):
        raise ValueError("Temperature must be a float")
    if not language or not isinstance(language, str):
        raise ValueError("Language must be a non-empty string")
