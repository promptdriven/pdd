import os
from rich import print as rprint
from rich.markdown import Markdown
from langchain_core.prompts import PromptTemplate
from langchain_core.output_parsers import JsonOutputParser, StrOutputParser
from langchain_community.cache import SQLiteCache
from langchain.globals import set_llm_cache
from .llm_selector import llm_selector
from .preprocess import preprocess

# Setup cache to save money and increase speeds
set_llm_cache(SQLiteCache(database_path=".langchain.db"))

def fix_errors_from_unit_tests(
    unit_test: str,
    code: str,
    prompt: str,
    error: str,
    error_file: str,
    strength: float,
    temperature: float
) -> tuple:
    """
    Fix errors in unit tests using LLM models.

    :param unit_test: The unit test code as a string.
    :param code: The code to be tested as a string.
    :param prompt: The prompt that generated the code under test.
    :param error: The error message from the unit test.
    :param error_file: Path to the file where error logs will be appended.
    :param strength: The strength parameter for LLM selection.
    :param temperature: The temperature parameter for LLM selection.
    :return: A tuple containing flags for updates, the fixed code and unit test, and total cost.
    """
    try:
        # Step 1: Load prompt files
        pdd_path = os.getenv('PDD_PATH')
        if not pdd_path:
            raise ValueError("PDD_PATH environment variable is not set")

        with open(os.path.join(pdd_path, 'prompts', 'fix_errors_from_unit_tests_LLM.prompt'), 'r') as file:
            fix_errors_prompt = file.read()

        with open(os.path.join(pdd_path, 'prompts', 'extract_unit_code_fix_LLM.prompt'), 'r') as file:
            extract_fix_prompt = file.read()

        # Step 2: Read contents of error_file
        try:
            with open(error_file, 'r') as file:
                existing_errors = file.read()
        except FileNotFoundError:
            existing_errors = ""
        except IOError as e:
            rprint(f"[bold red]Error reading error file: {e}[/bold red]")
            existing_errors = ""

        # Step 3: Create Langchain LCEL template for fix_errors_from_unit_tests
        fix_errors_template = PromptTemplate.from_template(fix_errors_prompt)

        # Step 4: Use llm_selector with provided strength and temperature
        llm, token_counter, input_cost, output_cost, model_name = llm_selector(strength, temperature)

        # Step 5: Run the code through the model using Langchain LCEL
        chain = fix_errors_template | llm | StrOutputParser()
        processed_prompt = preprocess(prompt, recursive=True, double_curly_brackets=False)
        input_data = {
            "unit_test": unit_test,
            "code": code,
            "prompt": processed_prompt,
            "errors": error
        }
        prompt_tokens = token_counter(str(input_data))
        cost_run_1 = (prompt_tokens / 1_000_000) * input_cost

        # 5b: Pretty print running message
        rprint(f"[bold green]Running fix_errors_from_unit_tests...[/bold green]")
        rprint(f"Prompt tokens: {prompt_tokens}, Cost: ${cost_run_1:.6f}")

        # Invoke the chain
        result_1 = chain.invoke(input_data)

        # 5c: Append output to error_file
        try:
            with open(error_file, 'a') as file:
                file.write("\n\n" + "="*50 + "\n")
                file.write("Fix Errors From Unit Tests Output:\n")
                file.write(result_1)
        except IOError as e:
            rprint(f"[bold red]Error writing to error file: {e}[/bold red]")

        # Step 6: Pretty print the markdown formatting and cost
        markdown_output = Markdown(result_1)
        rprint(markdown_output)
        result_tokens = token_counter(result_1)
        cost_result_1 = (result_tokens / 1_000_000) * output_cost
        rprint(f"Result tokens: {result_tokens}, Cost: ${cost_result_1:.6f}")

        # Append markdown output to error_file
        try:
            with open(error_file, 'a') as file:
                # file.write("\n\nMarkdown Output:\n")
                # file.write(result_1)
                file.write(f"\nResult tokens: {result_tokens}, Cost: ${cost_result_1:.6f}\n")
        except IOError as e:
            rprint(f"[bold red]Error writing markdown output to error file: {e}[/bold red]")

        # Step 7: Create a second Langchain LCEL template for extract_unit_code_fix
        extract_fix_template = PromptTemplate.from_template(extract_fix_prompt)

        # Step 8: Use llm_selector with strength 0.5 and provided temperature
        llm, token_counter, input_cost, output_cost, _ = llm_selector(0.9, temperature)
        parser = JsonOutputParser()

        # Step 9: Run the code through the model using Langchain LCEL
        chain = extract_fix_template | llm | parser
        input_data_2 = {
            "unit_test_fix": result_1,
            "unit_test": unit_test,
            "code": code
        }
        prompt_tokens_2 = token_counter(str(input_data_2))
        cost_run_2 = (prompt_tokens_2 / 1_000_000) * input_cost

        # 9b: Pretty print running message
        rprint(f"[bold green]Running extract_unit_code_fix...[/bold green]")
        rprint(f"Prompt tokens: {prompt_tokens_2}, Cost: ${cost_run_2:.6f}")

        # Invoke the chain
        result_2 = chain.invoke(input_data_2)

        result_tokens_2 = token_counter(str(result_2))
        cost_result_2 = (result_tokens_2 / 1_000_000) * output_cost

        # Step 10: Calculate the total cost
        total_cost = cost_run_1 + cost_result_1 + cost_run_2 + cost_result_2

        # Step 11: Print the total cost and return results
        rprint(f"Total cost of both runs: ${total_cost:.6f}")

        return (
            result_2.get('update_unit_test', False),
            result_2.get('update_code', False),
            result_2.get('fixed_unit_test', ''),
            result_2.get('fixed_code', ''),
            total_cost,
            model_name
        )

    except Exception as e:
        rprint(f"[bold red]An error occurred: {e}[/bold red]")
        return False, False, '', '', 0.0, ''