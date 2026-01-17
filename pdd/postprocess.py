from __future__ import annotations

import re
from typing import Tuple, Optional

from rich.console import Console
from pydantic import BaseModel, Field, ValidationError

from . import DEFAULT_STRENGTH, DEFAULT_TIME
from .load_prompt_template import load_prompt_template
from .llm_invoke import llm_invoke


console = Console()


class ExtractedCode(BaseModel):
    focus: str = Field("", description="Focus of the code")
    explanation: str = Field("", description="Explanation of the code")
    extracted_code: str = Field(..., description="Extracted code")


def postprocess_0(llm_output: str, language: str) -> str:
    """Simple extraction of code blocks."""
    if language == "prompt":
        # Strip <prompt> tags
        llm_output = re.sub(r"<prompt>\s*(.*?)\s*</prompt>", r"\1", llm_output, flags=re.DOTALL)
        llm_output = llm_output.strip()

        # Also strip triple backticks if present
        lines = llm_output.splitlines()
        if lines and lines[0].startswith("```"):
            # Remove first line with opening backticks
            lines = lines[1:]
            # If there's a last line with closing backticks, remove it
            if lines and lines[-1].startswith("```"):
                lines = lines[:-1]
        llm_output = "\n".join(lines)

        return llm_output.strip()

    # First try to find complete code blocks with closing backticks
    code_blocks = re.findall(r"```(?:[a-zA-Z]+)?\n(.*?)\n```", llm_output, re.DOTALL)
    if code_blocks:
        return "\n".join(block.strip() for block in code_blocks)

    # If no complete blocks found, try to find incomplete blocks (opening backticks without closing)
    # But ensure there's actual content after the opening backticks
    incomplete_match = re.search(r"```(?:[a-zA-Z]+)?\n(.+?)(?:\n```)?$", llm_output, re.DOTALL)
    if incomplete_match:
        content = incomplete_match.group(1).strip()
        # Don't return if content is just closing backticks
        if content and content != "```":
            return content

    return ""


def postprocess(
    llm_output: str,
    language: str,
    strength: float = DEFAULT_STRENGTH,
    temperature: float = 0.0,
    time: float = DEFAULT_TIME,
    verbose: bool = False,
) -> Tuple[str, float, str]:
    """
    Extracts code from a string output of an LLM.

    Args:
        llm_output: A string containing a mix of text and code sections.
        language: A string specifying the programming language of the code to be extracted.
        strength: A float between 0 and 1 that represents the strength of the LLM model to use.
        temperature: A float between 0 and 1 that represents the temperature parameter for the LLM model.
        time: A float between 0 and 1 that controls the thinking effort for the LLM model.
        verbose: A boolean that indicates whether to print detailed processing information.

    Returns:
        A tuple containing the extracted code string, total cost float and model name string.
    """
    if not isinstance(llm_output, str) or not llm_output:
        raise ValueError("llm_output must be a non-empty string")
    if not isinstance(language, str) or not language:
        raise ValueError("language must be a non-empty string")
    if not isinstance(strength, (int, float)):
        raise TypeError("strength must be a number")
    if not 0 <= strength <= 1:
        raise ValueError("strength must be between 0 and 1")
    if not isinstance(temperature, (int, float)):
        raise TypeError("temperature must be a number")
    if not 0 <= temperature <= 1:
        raise ValueError("temperature must be between 0 and 1")

    if language == "prompt":
        extracted_code = postprocess_0(llm_output, language)
        return extracted_code, 0.0, "simple_extraction"
    
    if strength == 0:
        extracted_code = postprocess_0(llm_output, language)
        if verbose:
            console.print("[blue]Using simple code extraction (strength = 0)[/blue]")
        return extracted_code, 0.0, "simple_extraction"

    prompt_name = "extract_code_LLM"
    prompt = load_prompt_template(prompt_name)

    if not prompt:
        error_msg = "Failed to load prompt template"
        console.print(f"[red]Error:[/red] {error_msg}")
        raise ValueError(error_msg)

    input_json = {"llm_output": llm_output, "language": language}

    if verbose:
        console.print("[blue]Loaded prompt template for code extraction[/blue]")

    try:
        result = llm_invoke(
            prompt=prompt,
            input_json=input_json,
            strength=strength,
            temperature=temperature,
            time=time,
            output_pydantic=ExtractedCode,
            verbose=verbose,
        )

        if not result or "result" not in result:
            error_msg = "Failed to get valid response from LLM"
            console.print(f"[red]Error during LLM invocation:[/red] {error_msg}")
            raise ValueError(error_msg)

        extracted_code = result["result"].extracted_code

        # Clean up triple backticks
        lines = extracted_code.splitlines()
        if lines and lines[0].startswith("```"):
            # Remove first line with opening backticks
            lines = lines[1:]
            # If there's a last line with closing backticks, remove it
            if lines and lines[-1].startswith("```"):
                lines = lines[:-1]
        extracted_code = "\n".join(lines)

        total_cost = result["cost"]
        model_name = result["model_name"]

        if verbose:
            console.print("[green]Successfully extracted code[/green]")

        return extracted_code, total_cost, model_name

    except KeyError as e:
        console.print(f"[red]Error in postprocess: {e}[/red]")
        raise ValueError(f"Failed to get valid response from LLM: missing key {e}")
    except Exception as e:
        console.print(f"[red]Error in postprocess: {e}[/red]")
        raise
