import os
from typing import Tuple
from langchain_core.prompts import PromptTemplate
from langchain_core.output_parsers import StrOutputParser, JsonOutputParser
from langchain_core.runnables import RunnablePassthrough
from rich import print as rprint
from rich.markdown import Markdown
from llm_selector import llm_selector


def xml_tagger(raw_prompt: str, strength: float, temperature: float) -> Tuple[str, float]:
    """
    Converts a raw prompt into XML format and extracts XML tags using Langchain.

    Args:
        raw_prompt (str): The input prompt to be converted.
        strength (float): The strength parameter for LLM selection.
        temperature (float): The temperature parameter for LLM selection.

    Returns:
        Tuple[str, float]: The extracted XML tags and the total cost of processing.
    """
    # Input validation
    if not isinstance(raw_prompt, str):
        raise TypeError("raw_prompt must be a string")
    if not isinstance(strength, (int, float)):
        raise TypeError("strength must be a number")
    if not isinstance(temperature, (int, float)):
        raise TypeError("temperature must be a number")

    try:
        # Step 1: Load prompts
        pdd_path = os.getenv('PDD_PATH')
        if not pdd_path:
            raise ValueError("PDD_PATH environment variable is not set")

        with open(f"{pdd_path}/prompts/xml_convertor_LLM.prompt", "r") as f:
            xml_convertor_prompt = f.read()
        with open(f"{pdd_path}/prompts/extract_xml_LLM.prompt", "r") as f:
            extract_xml_prompt = f.read()

        # Step 2 & 3: Create LCEL template and select LLM
        llm, token_counter, input_cost, output_cost = llm_selector(strength, temperature)

        # Step 4: Run XML conversion
        xml_convertor_template = PromptTemplate.from_template(xml_convertor_prompt)
        xml_convertor_chain = xml_convertor_template | llm | StrOutputParser()

        input_tokens = token_counter(raw_prompt)
        input_cost_usd = (input_tokens / 1_000_000) * input_cost
        rprint(f"[bold]Running XML conversion...[/bold]")
        rprint(f"Input tokens: {input_tokens}")
        rprint(f"Estimated input cost: ${input_cost_usd:.6f}")

        xml_generated_analysis = xml_convertor_chain.invoke({"raw_prompt": raw_prompt})

        # Step 5: Extract XML
        extract_xml_template = PromptTemplate.from_template(extract_xml_prompt)
        extract_xml_chain = extract_xml_template | llm | JsonOutputParser()

        extract_tokens = token_counter(xml_generated_analysis)
        extract_cost_usd = (extract_tokens / 1_000_000) * input_cost
        rprint(f"\n[bold]Extracting XML...[/bold]")
        rprint(f"Input tokens: {extract_tokens}")
        rprint(f"Estimated input cost: ${extract_cost_usd:.6f}")

        result = extract_xml_chain.invoke({"xml_generated_analysis": xml_generated_analysis})
        xml_tagged = result.get('xml_tagged', '')

        # Step 6: Pretty print result
        output_tokens = token_counter(xml_tagged)
        output_cost_usd = (output_tokens / 1_000_000) * output_cost
        rprint(f"\n[bold]Extracted XML:[/bold]")
        rprint(Markdown(f"```xml\n{xml_tagged}\n```"))
        rprint(f"Output tokens: {output_tokens}")
        rprint(f"Estimated output cost: ${output_cost_usd:.6f}")

        # Step 7: Calculate total cost
        total_cost = input_cost_usd + extract_cost_usd + output_cost_usd
        rprint(f"\n[bold]Total estimated cost: ${total_cost:.6f}[/bold]")

        # Step 8: Return results
        return xml_tagged, total_cost

    except Exception as e:
        rprint(f"[bold red]An error occurred: {str(e)}[/bold red]")
        return "", 0.0

# Example usage
if __name__ == "__main__":
    raw_prompt = "Write a story about a magical forest"
    strength = 0.7
    temperature = 0.5
    
    xml_tagged, total_cost = xml_tagger(raw_prompt, strength, temperature)