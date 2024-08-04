import os
from rich import print as rprint
from rich.markdown import Markdown
import tiktoken
from langchain_core.prompts import PromptTemplate
from langchain_openai import ChatOpenAI
from langchain_core.output_parsers import StrOutputParser
from langchain_community.cache import SQLiteCache
from langchain.globals import set_llm_cache
from llm_selector import llm_selector
from langchain_core.pydantic_v1 import BaseModel, Field
from langchain_core.output_parsers import PydanticOutputParser

# Setup cache to save money and increase speeds
set_llm_cache(SQLiteCache(database_path=".langchain.db"))

class FixResult(BaseModel):
    update_unit_test: bool = Field(description="Whether the unit test needs to be updated")
    update_code: bool = Field(description="Whether the code needs to be updated")
    fixed_unit_test: str = Field(description="The fixed unit test code")
    fixed_code: str = Field(description="The fixed main code")

def fix_errors_from_unit_tests(unit_test, code, error, strength):
    # Step 1: Load the prompt files
    pdd_path = os.getenv('PDD_PATH')
    with open(os.path.join(pdd_path, 'prompts', 'fix_errors_from_unit_tests_LLM.prompt'), 'r') as file:
        fix_errors_prompt = file.read()
    with open(os.path.join(pdd_path, 'prompts', 'extract_unit_code_fix_LLM.prompt'), 'r') as file:
        extract_fix_prompt = file.read()

    # Step 2: Create Langchain LCEL template from the fix_errors_from_unit_tests prompt
    fix_errors_template = PromptTemplate.from_template(fix_errors_prompt)

    # Step 3: Use llm_selector and a temperature of 0 for the llm model
    llm, input_cost, output_cost = llm_selector(strength, 0)

    # Step 4: Run the code through the model using Langchain LCEL
    chain = fix_errors_template | llm | StrOutputParser()
    prompt_input = {
        'unit_test': unit_test,
        'code': code,
        'errors': error
    }

    # Calculate token count and cost
    encoding = tiktoken.get_encoding("cl100k_base")
    token_count = len(encoding.encode(str(prompt_input)))
    cost = (token_count / 1_000_000) * input_cost

    rprint(f"[bold green]Running the model with {token_count} tokens. Estimated cost: ${cost:.6f}[/bold green]")

    result = chain.invoke(prompt_input)

    # Pretty print the markdown formatting in the result
    rprint(Markdown(result))
    result_token_count = len(encoding.encode(result))
    result_cost = (result_token_count / 1_000_000) * output_cost
    rprint(f"[bold green]Result contains {result_token_count} tokens. Estimated cost: ${result_cost:.6f}[/bold green]")
    total_cost = cost + result_cost
    rprint(f"[bold green]Total cost for this run: ${total_cost:.6f}[/bold green]")

    # Step 7: Create a second Langchain LCEL template from the extract_unit_code_fix prompt
    extract_fix_template = PromptTemplate.from_template(extract_fix_prompt)

    # Step 8: Use llm_selector with a strength setting of 0.5 and a temperature of 0
    llm, input_cost, output_cost = llm_selector(0.5, 0)
    parser = PydanticOutputParser(pydantic_object=FixResult)

    # Step 9: Run the code through the model using Langchain LCEL from Step 8
    chain = extract_fix_template | llm | parser
    prompt_input = {
        'unit_test_fix': result
    }

    # Calculate token count and cost
    token_count = len(encoding.encode(str(prompt_input)))
    cost = (token_count / 1_000_000) * input_cost

    rprint(f"[bold green]Running the model with {token_count} tokens. Estimated cost: ${cost:.6f}[/bold green]")

    result = chain.invoke(prompt_input)

    # Pretty print the result
    rprint(result)
    result_token_count = len(encoding.encode(str(result)))
    result_cost = (result_token_count / 1_000_000) * output_cost
    rprint(f"[bold green]Result contains {result_token_count} tokens. Estimated cost: ${result_cost:.6f}[/bold green]")
    total_cost += cost + result_cost
    rprint(f"[bold green]Total cost for both runs: ${total_cost:.6f}[/bold green]")

    # Step 10: Return the results
    return result.update_unit_test, result.update_code, result.fixed_unit_test, result.fixed_code