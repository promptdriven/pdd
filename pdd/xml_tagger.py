import os
from pathlib import Path
from typing import Tuple
from rich import print as rprint
from rich.markdown import Markdown
from langchain_core.prompts import PromptTemplate
from langchain_core.output_parsers import StrOutputParser, JsonOutputParser
from langchain_core.pydantic_v1 import BaseModel, Field
from .llm_selector import llm_selector


class XMLExtractResult(BaseModel):
    xml_tagged: str = Field(description="The extracted XML-tagged prompt")


def xml_tagger(raw_prompt: str, strength: float, temperature: float) -> Tuple[str, float, str]:
    """
    Converts a raw prompt into XML format using a language model and extracts the XML content.

    Args:
        raw_prompt (str): The raw input prompt to be processed.
        strength (float): The strength parameter for the language model.
        temperature (float): The temperature parameter for the language model.

    Returns:
        Tuple[str, float, str]: A tuple containing the XML-tagged string, the total cost of processing, and the model name.
    """
    try:
        # Step 1: Load prompt files
        pdd_path = os.getenv('PDD_PATH')
        if not pdd_path:
            raise ValueError("PDD_PATH environment variable is not set")

        with open(Path(pdd_path) / 'prompts' / 'xml_convertor_LLM.prompt', 'r') as f:
            xml_convertor_prompt = f.read()
        with open(Path(pdd_path) / 'prompts' / 'extract_xml_LLM.prompt', 'r') as f:
            extract_xml_prompt = f.read()

        # Step 2 & 3: Create LCEL template and use llm_selector
        xml_convertor_template = PromptTemplate.from_template(xml_convertor_prompt)
        llm, token_counter, input_cost, output_cost, model_name = llm_selector(strength, temperature)

        # Step 4: Run the code through the model
        xml_chain = xml_convertor_template | llm | StrOutputParser()
        token_count = token_counter(raw_prompt)
        prompt_cost = (token_count / 1_000_000) * input_cost

        rprint(f"[bold]Running XML conversion...[/bold]")
        rprint(f"Tokens in prompt: {token_count}")
        rprint(f"Estimated cost: ${prompt_cost:.6f}")

        xml_generated_analysis = xml_chain.invoke({"raw_prompt": raw_prompt})

        # Step 5: Extract XML using a different model
        extract_llm, extract_token_counter, extract_input_cost, extract_output_cost, extract_model_name = llm_selector(0.9, temperature)
        extract_template = PromptTemplate.from_template(extract_xml_prompt)
        extract_chain = extract_template | extract_llm | JsonOutputParser(pydantic_object=XMLExtractResult)

        extract_token_count = extract_token_counter(xml_generated_analysis)
        extract_prompt_cost = (extract_token_count / 1_000_000) * extract_input_cost

        rprint(f"[bold]Extracting XML...[/bold]")
        rprint(f"Tokens in analysis: {extract_token_count}")
        rprint(f"Estimated cost: ${extract_prompt_cost:.6f}")

        extract_result = extract_chain.invoke({"xml_generated_analysis": xml_generated_analysis})

        # Step 6: Pretty print the result
        xml_tagged = extract_result.get('xml_tagged', '')
        result_token_count = token_counter(xml_tagged)
        result_cost = (result_token_count / 1_000_000) * output_cost

        rprint(Markdown(xml_tagged))
        rprint(f"Tokens in result: {result_token_count}")
        rprint(f"Estimated result cost: ${result_cost:.6f}")

        # Step 7: Calculate total cost
        total_cost = prompt_cost + extract_prompt_cost + result_cost

        # Step 8: Return results
        return xml_tagged, total_cost, model_name

    except FileNotFoundError as e:
        rprint(f"[bold red]Error:[/bold red] {e}")
        return "", 0.0, ""
    except ValueError as e:
        rprint(f"[bold red]Error:[/bold red] {e}")
        return "", 0.0, ""
    except Exception as e:
        rprint(f"[bold red]An unexpected error occurred:[/bold red] {e}")
        return "", 0.0, ""
