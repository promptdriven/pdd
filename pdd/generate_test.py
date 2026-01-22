"""
Module for generating unit tests from code or example files using LLMs.
"""
from __future__ import annotations

import re
from typing import Optional, Tuple

from rich.console import Console
from rich.markdown import Markdown

from pdd import DEFAULT_STRENGTH, DEFAULT_TIME, EXTRACTION_STRENGTH
from pdd.continue_generation import continue_generation
from pdd.llm_invoke import llm_invoke
from pdd.load_prompt_template import load_prompt_template
from pdd.postprocess import postprocess
from pdd.preprocess import preprocess
from pdd.unfinished_prompt import unfinished_prompt

console = Console()


def _validate_inputs(
    prompt: str,
    code: Optional[str],
    strength: float,
    temperature: float,
    language: str
) -> None:
    """
    Validates the inputs for generate_test function.

    Raises:
        ValueError: If any input is invalid.
    """
    if not isinstance(prompt, str) or not prompt.strip():
        raise ValueError("Prompt must be a non-empty string")

    if code is None or not isinstance(code, str) or not code.strip():
        raise ValueError("Code must be a non-empty string")

    if not isinstance(strength, (int, float)) or not 0 <= strength <= 1:
        raise ValueError("Strength must be a float between 0 and 1")

    if not isinstance(temperature, (int, float)):
        raise ValueError("Temperature must be a float")

    if not isinstance(language, str) or not language.strip():
        raise ValueError("Language must be a non-empty string")


def _inject_sys_path_preamble(code: str) -> str:
    """
    Injects sys.path isolation preamble into Python code.
    Ensures it appears after __future__ imports but before other imports.
    """
    preamble = (
        "\nimport sys\n"
        "from pathlib import Path\n\n"
        "# Add project root to sys.path to ensure local code is prioritized\n"
        "# This allows testing local changes without installing the package\n"
        "project_root = Path(__file__).resolve().parents[1]\n"
        "sys.path.insert(0, str(project_root))\n"
    )
    
    lines = code.splitlines()
    insert_idx = 0
    
    # Skip shebang
    if lines and len(lines) > insert_idx and lines[insert_idx].startswith("#!"):
        insert_idx += 1
        
    # Skip encoding
    if lines and len(lines) > insert_idx and lines[insert_idx].startswith("# -*-"):
        insert_idx += 1
        
    # Skip __future__ imports and initial comments/blanks
    while insert_idx < len(lines):
        line = lines[insert_idx].strip()
        if not line:
            insert_idx += 1
            continue
        if line.startswith("#"):
            insert_idx += 1
            continue
        if line.startswith("from __future__"):
            insert_idx += 1
            continue
        
        # Found something that is not a comment, empty, or future import.
        break
            
    lines.insert(insert_idx, preamble)
    return "\n".join(lines)


def generate_test(
    prompt: str,
    code: Optional[str] = None,
    example: Optional[str] = None,
    strength: float = DEFAULT_STRENGTH,
    temperature: float = 0.0,
    time: float = DEFAULT_TIME,
    language: str = 'python',
    verbose: bool = False,
    source_file_path: Optional[str] = None,
    test_file_path: Optional[str] = None,
    module_name: Optional[str] = None,
    existing_tests: Optional[str] = None
) -> Tuple[str, float, str]:
    """
    Generates a unit test for a given code file or example usage using an LLM.

    Args:
        prompt: The prompt that generated the code (context).
        code: The source code to test. Mutually exclusive with 'example'.
        example: An example usage of the module. Mutually exclusive with 'code'.
        strength: LLM strength (0.0 to 1.0).
        temperature: LLM temperature.
        time: Thinking effort for the LLM (0.0 to 1.0).
        language: Target language for the test.
        verbose: Whether to print detailed logs.
        source_file_path: Path to the code under test.
        test_file_path: Destination path for the test.
        module_name: Name of the module for imports.
        existing_tests: Content of existing tests to merge.

    Returns:
        Tuple containing:
        - unit_test (str): The generated test code.
        - total_cost (float): Total cost of generation.
        - model_name (str): Name of the model used.
    """
    total_cost = 0.0
    model_name = "unknown"

    # --- Step 1: Determine prompt template and validate inputs ---
    if (code is None and example is None) or (code is not None and example is not None):
        raise ValueError("Exactly one of 'code' or 'example' must be provided.")

    template_name = "generate_test_from_example_LLM" if example else "generate_test_LLM"

    raw_template = load_prompt_template(template_name)
    if not raw_template:
        raise ValueError(f"Failed to load {template_name} prompt template")

    # --- Step 2: Preprocess template and prompt ---
    # Preprocess the template
    prompt_template = preprocess(
        raw_template,
        recursive=False,
        double_curly_brackets=False
    )

    # Preprocess the original prompt input
    processed_prompt_input = preprocess(
        prompt,
        recursive=False,
        double_curly_brackets=False
    )

    # --- Step 3: Run inputs through LLM ---
    input_data = {
        "prompt_that_generated_code": processed_prompt_input,
        "language": language,
        "source_file_path": source_file_path if source_file_path else "",
        "test_file_path": test_file_path if test_file_path else "",
        "module_name": module_name if module_name else "",
        "existing_tests": existing_tests if existing_tests else ""
    }

    if example:
        input_data["example"] = example
    else:
        input_data["code"] = code

    if verbose:
        console.print(
            f"[bold blue]Generating unit test using template: {template_name}[/bold blue]"
        )
        console.print(f"[dim]Strength: {strength}, Time: {time}, Temp: {temperature}[/dim]")

    try:
        llm_result = llm_invoke(
            prompt=prompt_template,
            input_json=input_data,
            strength=strength,
            temperature=temperature,
            time=time,
            verbose=verbose
        )
    except Exception as e:
        console.print(f"[bold red]Error invoking LLM:[/bold red] {e}")
        raise

    current_text = llm_result['result']
    total_cost += llm_result.get('cost', 0.0)
    model_name = llm_result.get('model_name', 'unknown')

    # --- Step 4: Verbose Output of Initial Result ---
    if verbose:
        console.print("[bold green]Initial LLM Output:[/bold green]")
        console.print(Markdown(current_text))
        console.print(f"[dim]Initial Cost: ${llm_result.get('cost', 0.0):.6f}[/dim]")

    # --- Step 5: Detect incomplete generation ---
    # Check the last 600 characters
    last_chunk = current_text[-600:] if len(current_text) > 600 else current_text

    # Only check if there is actual content
    if last_chunk.strip():
        try:
            reasoning, is_finished, check_cost, _ = unfinished_prompt(
                prompt_text=last_chunk,
                strength=strength,
                temperature=temperature,
                time=time,
                language=language,
                verbose=verbose
            )
            total_cost += check_cost

            if not is_finished:
                if verbose:
                    console.print(
                        "[yellow]Output detected as incomplete. Continuing generation...[/yellow]"
                    )
                    console.print(f"[dim]Reasoning: {reasoning}[/dim]")

                # We need the formatted prompt for continue_generation.
                # Since llm_invoke handles formatting internally, we attempt to format here
                # to pass context to the continuation logic.
                try:
                    formatted_input_prompt = prompt_template.format(**input_data)
                except Exception:
                    # Fallback if simple formatting fails (e.g. complex jinja or missing keys)
                    # We use the raw template as best effort context
                    formatted_input_prompt = prompt_template

                final_llm_output, cont_cost, cont_model = continue_generation(
                    formatted_input_prompt=formatted_input_prompt,
                    llm_output=current_text,
                    strength=strength,
                    temperature=temperature,
                    verbose=verbose
                )

                current_text = final_llm_output
                total_cost += cont_cost
                model_name = cont_model # Update to the model used for continuation
        except Exception as e:
            console.print(f"[bold red]Error during completion check/continuation:[/bold red] {e}")
            # Proceed with what we have if check fails

    # --- Step 6: Postprocess ---
    try:
        extracted_code, pp_cost, _ = postprocess(
            llm_output=current_text,
            language=language,
            strength=EXTRACTION_STRENGTH,
            verbose=verbose
        )
        total_cost += pp_cost
        unit_test = extracted_code
    except Exception as e:
        if verbose:
            console.print(f"[bold red]Postprocessing failed:[/bold red] {e}")
        unit_test = ""

    # Fallback extraction if postprocess returned empty or failed
    if not unit_test.strip():
        if verbose:
            console.print(
                "[yellow]Postprocess returned empty. Attempting fallback regex extraction.[/yellow]"
            )

        # Regex to find code blocks, preferring those with specific keywords
        code_block_pattern = re.compile(r"```(?:\w+)?\n(.*?)```", re.DOTALL)
        matches = code_block_pattern.findall(current_text)

        best_match = ""
        for match in matches:
            # Heuristic: prefer blocks that look like tests
            if "def test_" in match or "import unittest" in match or "import pytest" in match:
                best_match = match
                break

        if not best_match and matches:
            # If no specific test keywords found, take the longest block
            best_match = max(matches, key=len)

        unit_test = best_match if best_match else current_text

    # --- Step 6.5: Inject sys.path isolation for Python ---
    if language.lower() == 'python' and unit_test.strip() and "sys.path.insert" not in unit_test:
        unit_test = _inject_sys_path_preamble(unit_test)

    # --- Step 7: Final Cost Reporting ---
    if verbose:
        console.print(f"[bold blue]Generation Complete.[/bold blue]")
        console.print(f"[bold]Total Cost:[/bold] ${total_cost:.6f}")
        console.print(f"[dim]Final Model: {model_name}[/dim]")

    # --- Step 8: Return ---
    return unit_test, total_cost, model_name