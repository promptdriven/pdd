import os
from rich import print as rprint
from rich.markdown import Markdown
import tiktoken
from langchain_core.prompts import PromptTemplate
from langchain_core.output_parsers import StrOutputParser, JsonOutputParser
from llm_selector import llm_selector
from langchain_core.runnables import RunnablePassthrough

def xml_tagger(raw_prompt, strength, temperature):
    try:
        # Step 1: Load the prompt files
        pdd_path = os.getenv('PDD_PATH')
        if not pdd_path:
            raise ValueError("PDD_PATH environment variable is not set")

        with open(os.path.join(pdd_path, 'prompts/xml_convertor_LLM.prompt'), 'r') as file:
            xml_convertor_prompt = file.read()

        with open(os.path.join(pdd_path, 'prompts/extract_xml_LLM.prompt'), 'r') as file:
            extract_xml_prompt = file.read()

        # Step 2: Create a Langchain LCEL template from xml_convertor prompt
        xml_convertor_template = PromptTemplate.from_template(xml_convertor_prompt)

        # Step 3: Use the llm_selector function for the LLM model
        llm, input_cost, output_cost = llm_selector(strength, temperature)

        # Step 4: Run the code through the model using Langchain LCEL
        chain = xml_convertor_template | llm | StrOutputParser()

        # Step 4a: Pass the 'raw_prompt' to the prompt
        encoding = tiktoken.get_encoding("cl100k_base")
        token_count = len(encoding.encode(raw_prompt))
        rprint(f"[bold green]Running XML conversion...[/bold green]")
        rprint(f"Token count: {token_count}, Cost: ${input_cost * token_count / 1_000_000:.6f}")

        xml_generated_analysis = chain.invoke({"raw_prompt": raw_prompt})

        # Step 5: Create a Langchain LCEL template from the extract_xml prompt
        extract_xml_template = PromptTemplate.from_template(extract_xml_prompt)
        parser = JsonOutputParser()

        chain = extract_xml_template | llm | parser

        # Step 5a: Pass the 'xml_generated_analysis' to the prompt
        token_count = len(encoding.encode(xml_generated_analysis))
        rprint(f"[bold green]Extracting XML...[/bold green]")
        rprint(f"Token count: {token_count}, Cost: ${output_cost * token_count / 1_000_000:.6f}")

        result = chain.invoke({"xml_generated_analysis": xml_generated_analysis})

        # Step 6: Pretty print the extracted tagged prompt
        xml_tagged = result['xml_tagged']
        rprint(Markdown(xml_tagged))
        token_count = len(encoding.encode(xml_tagged))
        rprint(f"Token count: {token_count}, Cost: ${output_cost * token_count / 1_000_000:.6f}")

        # Step 7: Return the 'xml_tagged' string
        return xml_tagged

    except Exception as e:
        rprint(f"[bold red]Error:[/bold red] {e}")
        return None
