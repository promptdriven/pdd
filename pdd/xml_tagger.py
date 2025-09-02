"""XML tagging module for improving prompt structure with XML tags.

This module provides functionality to enhance LLM prompts by adding XML tags,
making them more structured and readable for better processing.
"""

from typing import Tuple
from rich import print as rprint
from rich.markdown import Markdown
from pydantic import BaseModel, Field
from .load_prompt_template import load_prompt_template
from .llm_invoke import llm_invoke
from . import EXTRACTION_STRENGTH
from . import DEFAULT_TIME

class XMLOutput(BaseModel):
    """Pydantic model for XML-tagged prompt output."""
    xml_tagged: str = Field(description="The XML-tagged version of the prompt")

def xml_tagger(
    raw_prompt: str,
    strength: float,
    temperature: float,
    verbose: bool = False,
    time: float = DEFAULT_TIME
) -> Tuple[str, float, str]:
    """
    Enhance a given LLM prompt by adding XML tags to improve its structure and readability.

    Args:
        raw_prompt (str): The prompt that needs XML tagging
        strength (float): The strength parameter for the LLM model (0-1)
        temperature (float): The temperature parameter for the LLM model (0-1)
        verbose (bool): Whether to print detailed information
        time (float): The time allocation for the LLM calls

    Returns:
        Tuple[str, float, str]: (xml_tagged, total_cost, model_name)
    """
    try:
        # Input validation
        if not raw_prompt or not isinstance(raw_prompt, str):
            raise ValueError("raw_prompt must be a non-empty string")
        if not 0 <= strength <= 1:
            raise ValueError("strength must be between 0 and 1")
        if not 0 <= temperature <= 1:
            raise ValueError("temperature must be between 0 and 1")

        total_cost = 0.0
        model_name = ""

        # Step 1: Load prompt templates
        xml_converter_prompt = load_prompt_template("xml_convertor_LLM")
        extract_xml_prompt = load_prompt_template("extract_xml_LLM")

        if not xml_converter_prompt or not extract_xml_prompt:
            raise ValueError("Failed to load prompt templates")

        # Step 2: First LLM invoke for XML conversion
        if verbose:
            rprint("[blue]Running XML conversion...[/blue]")

        conversion_response = llm_invoke(
            prompt=xml_converter_prompt,
            input_json={"raw_prompt": raw_prompt},
            strength=strength,
            temperature=temperature,
            verbose=verbose,
            time=time
        )

        xml_generated_analysis = conversion_response.get('result', '')
        total_cost += conversion_response.get('cost', 0.0)
        model_name = conversion_response.get('model_name', '')

        if verbose:
            rprint("[green]Intermediate XML result:[/green]")
            rprint(Markdown(xml_generated_analysis))

        # Step 3: Second LLM invoke for XML extraction
        if verbose:
            rprint("[blue]Extracting final XML structure...[/blue]")

        extraction_response = llm_invoke(
            prompt=extract_xml_prompt,
            input_json={"xml_generated_analysis": xml_generated_analysis},
            strength=EXTRACTION_STRENGTH,  # Fixed strength for extraction
            temperature=temperature,
            verbose=verbose,
            output_pydantic=XMLOutput,
            time=time
        )

        result: XMLOutput = extraction_response.get('result')
        total_cost += extraction_response.get('cost', 0.0)

        # Step 4: Print results if verbose
        if verbose:
            rprint("[green]Final XML-tagged prompt:[/green]")
            rprint(Markdown(result.xml_tagged))
            rprint(f"[yellow]Total cost: ${total_cost:.6f}[/yellow]")
            rprint(f"[yellow]Model used: {model_name}[/yellow]")

        # Step 5 & 6: Return results
        return result.xml_tagged, total_cost, model_name

    except Exception as error:
        rprint(f"[red]Error in xml_tagger: {str(error)}[/red]")
        raise

def main():
    """Example usage of the xml_tagger function"""
    try:
        sample_prompt = """
        Write a function that calculates the factorial of a number.
        The function should handle negative numbers and return appropriate error messages.
        Include examples of usage and error cases.
        """

        tagged_result, cost, model = xml_tagger(
            raw_prompt=sample_prompt,
            strength=0.7,
            temperature=0.8,
            verbose=True,
            time=0.5
        )

        rprint("[blue]XML Tagging Complete[/blue]")
        rprint(f"Total Cost: ${cost:.6f}")
        rprint(f"Model Used: {model}")
        rprint(f"Result length: {len(tagged_result)}")

    except Exception as error:
        rprint(f"[red]Error in main: {str(error)}[/red]")

if __name__ == "__main__":
    main()
