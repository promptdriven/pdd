import os
from rich import print as rprint
from rich.markdown import Markdown
import tiktoken
from langchain_core.prompts import PromptTemplate
from langchain_core.output_parsers import StrOutputParser
from langchain_community.cache import SQLiteCache
from langchain.globals import set_llm_cache
from langchain_core.pydantic_v1 import BaseModel, Field
from langchain_core.output_parsers import PydanticOutputParser
from llm_selector import llm_selector

# Setup cache to save money and increase speeds
set_llm_cache(SQLiteCache(database_path=".langchain.db"))

class FixResult(BaseModel):
    update_unit_test: bool = Field(description="Whether the unit test needs to be updated")
    update_code: bool = Field(description="Whether the code needs to be updated")
    fixed_unit_test: str = Field(description="The fixed unit test code")
    fixed_code: str = Field(description="The fixed main code")

def fix_errors_from_unit_tests(unit_test, code, error, strength):
    try:
        # Load the prompt files
        pdd_path = os.getenv('PDD_PATH', '.')
        with open(os.path.join(pdd_path, './prompts/fix_errors_from_unit_tests_LLM.prompt'), 'r') as file:
            fix_errors_prompt = file.read()
        with open(os.path.join(pdd_path, './prompts/extract_unit_code_fix_LLM.prompt'), 'r') as file:
            extract_fix_prompt = file.read()

        # Create Langchain LCEL template from the fix_errors_from_unit_tests prompt
        fix_errors_template = PromptTemplate.from_template(fix_errors_prompt)

        # Use llm_selector and a temperature of 0 for the llm model
        llm, input_cost, output_cost = llm_selector(strength, 0)

        # Create the chain
        chain = (fix_errors_template 
                 | llm 
                 | StrOutputParser())

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
        if isinstance(result, str):
            rprint(Markdown(result))
        else:
            rprint(f"Result: {result}")

        result_token_count = len(encoding.encode(str(result)))
        result_cost = (result_token_count / 1_000_000) * output_cost
        rprint(f"[bold green]Result contains {result_token_count} tokens. Estimated cost: ${result_cost:.6f}[/bold green]")
        total_cost = cost + result_cost
        rprint(f"[bold green]Total cost for this run: ${total_cost:.6f}[/bold green]")

        # Create a second Langchain LCEL template from the extract_unit_code_fix prompt
        extract_fix_template = PromptTemplate.from_template(extract_fix_prompt)

        # Use llm_selector with a strength setting of 0.5 and a temperature of 0
        llm, input_cost, output_cost = llm_selector(0.5, 0)
        parser = PydanticOutputParser(pydantic_object=FixResult)

        # Create the second chain
        chain = (extract_fix_template 
                 | llm 
                 | parser)

        prompt_input = {
            'unit_test_fix': result
        }

        # Calculate token count and cost
        token_count = len(encoding.encode(str(prompt_input)))
        cost = (token_count / 1_000_000) * input_cost

        rprint(f"[bold green]Running the model with {token_count} tokens. Estimated cost: ${cost:.6f}[/bold green]")

        result = chain.invoke(prompt_input)

        if isinstance(result, FixResult):
            return result.update_unit_test, result.update_code, result.fixed_unit_test, result.fixed_code
        elif isinstance(result, str):
            rprint(f"[bold yellow]Received string result from second chain: {result}[/bold yellow]")
            # Attempt to parse the string result
            lines = result.strip().split('\n')
            update_unit_test = any('update unit test: true' in line.lower() for line in lines)
            update_code = any('update code: true' in line.lower() for line in lines)
            
            # Extract fixed unit test
            fixed_unit_test = extract_code_block(lines, 'def test_')
            
            # Extract fixed code
            fixed_code = extract_code_block(lines, 'def ', exclude='def test_')
            
            return update_unit_test, update_code, fixed_unit_test, fixed_code
        else:
            rprint(f"[bold red]Unexpected result type: {type(result)}[/bold red]")
            return False, False, "", ""

    except Exception as e:
        rprint(f"[bold red]An error occurred: {str(e)}[/bold red]")
        return False, False, "", ""

def extract_code_block(lines, start_condition, exclude=None):
    code_lines = []
    in_block = False
    for line in lines:
        stripped_line = line.strip()
        if stripped_line.startswith(start_condition) and (not exclude or not stripped_line.startswith(exclude)):
            in_block = True
        if in_block:
            code_lines.append(stripped_line)
        if in_block and not stripped_line:
            break
    return normalize_indentation('\n'.join(code_lines).rstrip())

def normalize_indentation(code):
    lines = code.split('\n')
    if not lines:
        return ''
    
    # Find the indentation of the first non-empty line
    first_line = next((line for line in lines if line.strip()), '')
    initial_indent = len(first_line) - len(first_line.lstrip())
    
    # Remove the initial indentation from all lines
    normalized_lines = [line[initial_indent:] if line.startswith(' ' * initial_indent) else line for line in lines]
    
    # Ensure the first line has no indentation and the rest have 4 spaces
    result = [normalized_lines[0]]
    result.extend('    ' + line if line.strip() else line for line in normalized_lines[1:])
    
    return '\n'.join(result)