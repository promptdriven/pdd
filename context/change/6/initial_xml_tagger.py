import os
import tiktoken
from rich import print as rprint
from rich.markdown import Markdown
from langchain_core.prompts import PromptTemplate
from langchain_core.output_parsers import StrOutputParser, JsonOutputParser
from langchain_core.pydantic_v1 import BaseModel, Field
from langchain_community.cache import SQLiteCache
from langchain.globals import set_llm_cache
from llm_selector import llm_selector

# Ensure cache is set up
set_llm_cache(SQLiteCache(database_path=".langchain.db"))

# Define a Pydantic model for JSON output
class XMLTaggedOutput(BaseModel):
    xml_tagged: str = Field(description="The XML tagged prompt")

def xml_tagger(raw_prompt: str, strength: float, temperature: float) -> str:
    """
    Process a raw prompt to apply XML tagging using Langchain.

    :param raw_prompt: The input prompt to be processed.
    :param strength: The strength parameter for LLM selection.
    :param temperature: The temperature parameter for LLM selection.
    :return: The XML tagged prompt as a string.
    """
    try:
        # Step 1: Load the prompt files
        pdd_path = os.getenv('PDD_PATH')
        if not pdd_path:
            raise ValueError("PDD_PATH environment variable is not set")

        with open(os.path.join(pdd_path, 'prompts/xml_convertor_LLM.prompt'), 'r') as file:
            xml_convertor_prompt = file.read()

        with open(os.path.join(pdd_path, 'prompts/extract_xml_LLM.prompt'), 'r') as file:
            extract_xml_prompt = file.read()

        # Step 2: Create LCEL template from xml_convertor prompt
        xml_convertor_template = PromptTemplate.from_template(xml_convertor_prompt)

        # Step 3: Use the llm_selector function
        llm, input_cost, output_cost = llm_selector(strength, temperature)

        # Step 4: Run the code through the model using Langchain LCEL
        chain = xml_convertor_template | llm | StrOutputParser()

        # Token count and cost calculation
        encoding = tiktoken.get_encoding("cl100k_base")
        token_count = len(encoding.encode(raw_prompt))
        cost = (token_count / 1_000_000) * input_cost

        rprint(f"[bold green]Running XML conversion...[/bold green]")
        rprint(f"Token count: {token_count}, Cost: ${cost:.6f}")

        # Invoke the chain
        xml_generated_analysis = chain.invoke({"raw_prompt": raw_prompt})

        # Step 5: Create LCEL template from extract_xml prompt
        extract_xml_template = PromptTemplate.from_template(extract_xml_prompt)
        parser = JsonOutputParser(pydantic_object=XMLTaggedOutput)

        chain = extract_xml_template | llm | parser

        # Token count and cost calculation for the second step
        token_count = len(encoding.encode(xml_generated_analysis))
        cost = (token_count / 1_000_000) * output_cost

        rprint(f"[bold green]Extracting XML...[/bold green]")
        rprint(f"Token count: {token_count}, Cost: ${cost:.6f}")

        # Invoke the chain
        result = chain.invoke({"xml_generated_analysis": xml_generated_analysis})

        # Step 6: Pretty print the extracted tagged prompt
        xml_tagged = result['xml_tagged']
        rprint(Markdown(xml_tagged))
        rprint(f"Token count in result: {len(encoding.encode(xml_tagged))}, Cost: ${(len(encoding.encode(xml_tagged)) / 1_000_000) * output_cost:.6f}")

        # Step 7: Return the 'xml_tagged' string
        return xml_tagged

    except Exception as e:
        rprint(f"[bold red]Error:[/bold red] {e}")
        return ""

# Example usage
# xml_tagger("Tell me a joke about cats", 0.5, 0.7)