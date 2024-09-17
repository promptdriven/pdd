import os
from rich.console import Console
from rich.markdown import Markdown
from .preprocess import preprocess
from langchain_core.prompts import PromptTemplate
from langchain_core.output_parsers import JsonOutputParser
from langchain_core.output_parsers import StrOutputParser
from langchain_community.cache import SQLiteCache
from langchain.globals import set_llm_cache
from .llm_selector import llm_selector
from langchain.globals import set_debug
import json

set_debug(False)

# Set up the Rich console for pretty printing
console = Console()

# Set up cache to save money and increase speeds
set_llm_cache(SQLiteCache(database_path=".langchain.db"))

def split(input_prompt: str, input_code: str, example_code: str, strength: float, temperature: float):
    """
    Splits the input code using a language model and extracts sub-prompts.

    :param input_prompt: The initial prompt to be processed.
    :param input_code: The code to be split by the LLM.
    :param example_code: Example code to guide the LLM.
    :param strength: The strength parameter for LLM selection.
    :param temperature: The temperature parameter for LLM selection.
    :return: A tuple containing the sub-prompt, modified prompt, and total cost.
    """
    total_cost = 0.0
    sub_prompt = ""
    modified_prompt = ""
    
    try:
        # Step 1: Load the prompt files
        pdd_path = os.getenv('PDD_PATH', '.')
        with open(f'{pdd_path}/prompts/split_LLM.prompt', 'r') as file:
            split_llm_prompt = file.read()
        with open(f'{pdd_path}/prompts/extract_prompt_split_LLM.prompt', 'r') as file:
            extract_prompt_split_llm = file.read()

        # Step 2: Preprocess the split_LLM prompt
        processed_split_llm_prompt = preprocess(split_llm_prompt, recursive=False, double_curly_brackets=True, exclude_keys=['input_prompt', 'input_code', 'example_code'])

        # Step 3: Create a Langchain LCEL template
        prompt_template = PromptTemplate.from_template(processed_split_llm_prompt)

        # Step 4: Use the llm_selector function
        try:
            llm, token_counter, input_cost, output_cost, model_name = llm_selector(strength, temperature)
        except ValueError as e:
            console.print(f"[bold red]Error in llm_selector:[/bold red] {e}")
            raise

        # Step 4a: Run the input through the model
        chain = prompt_template | llm | StrOutputParser()
        llm_output = chain.invoke({
            "input_prompt": input_prompt,
            "input_code": input_code,
            "example_code": example_code
        })

        # Calculate token counts and costs
        input_tokens = token_counter(input_prompt + input_code + example_code)
        output_tokens = token_counter(llm_output)
        total_cost = (input_tokens * input_cost + output_tokens * output_cost) / 1_000_000

        # Pretty print the output
        console.print(Markdown(f"**LLM Output:**\n{llm_output}"))
        console.print(f"Input Tokens: {input_tokens}, Output Tokens: {output_tokens}, Estimated Cost: ${total_cost:.6f}")

        # Step 5: Create a Langchain LCEL template for JSON output
        processed_extract_prompt = preprocess(extract_prompt_split_llm, recursive=False, double_curly_brackets=False)
        json_parser = JsonOutputParser()
        json_prompt_template = PromptTemplate.from_template(processed_extract_prompt)

        try:
            llm_extract, token_counter_extract, input_cost_extract, output_cost_extract, model_name = llm_selector(.8, temperature)
        except ValueError as e:
            console.print(f"[bold red]Error in llm_selector:[/bold red] {e}")
            raise

        # Step 5a: Run the JSON extraction
        json_chain = json_prompt_template | llm_extract | json_parser
        try:
            json_output = json_chain.invoke({"llm_output": llm_output})
            
            # Print raw JSON output for debugging
            console.print(f"Raw JSON output: {json_output}")
            
            # Extract sub_prompt and modified_prompt
            if isinstance(json_output, dict):
                sub_prompt = json_output.get('sub_prompt', '')
                modified_prompt = json_output.get('modified_prompt', '')
                if not sub_prompt or not modified_prompt:
                    console.print("[bold yellow]Warning:[/bold yellow] sub_prompt or modified_prompt is empty in JSON output.")
            else:
                raise ValueError(f"JSON output is not a dictionary. Type: {type(json_output)}, Value: {json_output}")
        except Exception as e:
            console.print(f"[bold red]Error in JSON parsing:[/bold red] {e}")
            raise

        # Pretty print the extracted prompts
        console.print(Markdown(f"**Sub Prompt:**\n{sub_prompt}"))
        console.print(Markdown(f"**Modified Prompt:**\n{modified_prompt}"))

    except Exception as e:
        console.print(f"[bold red]An error occurred:[/bold red] {e}")
        raise

    # Return the results
    return sub_prompt, modified_prompt, total_cost

# Example usage
if __name__ == "__main__":
    sub_prompt, modified_prompt, total_cost = split(
        input_prompt="Your input prompt here",
        input_code="Generated code here",
        example_code="Example code here",
        strength=0.7,
        temperature=0.5
    )
    console.print(f"Sub Prompt: {sub_prompt}")
    console.print(f"Modified Prompt: {modified_prompt}")
    console.print(f"Total Cost: ${total_cost:.6f}")
