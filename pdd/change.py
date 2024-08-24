import os
from typing import Tuple
from rich.console import Console
from rich.markdown import Markdown
from preprocess import preprocess
from llm_selector import llm_selector
from langchain_core.prompts import PromptTemplate
from langchain_core.output_parsers import StrOutputParser, JsonOutputParser
from langchain.globals import set_debug

console = Console()

def change(input_prompt: str, input_code: str, change_prompt: str, strength: float, temperature: float) -> Tuple[str, float, str]:
    """
    Processes input prompts using a language model to generate and extract modified prompts.

    Args:
        input_prompt (str): The initial input prompt.
        input_code (str): The input code to be modified.
        change_prompt (str): The prompt describing the changes to be made.
        strength (float): The strength parameter for the language model.
        temperature (float): The temperature parameter for the language model.

    Returns:
        Tuple[str, float, str]: A tuple containing the modified prompt, total cost, and model name.
    """
    try:
        pdd_path = os.getenv('PDD_PATH', '')
        with open(f'{pdd_path}/prompts/xml/change_LLM.prompt', 'r') as file:
            change_llm_prompt = file.read()
        with open(f'{pdd_path}/prompts/extract_prompt_change_LLM.prompt', 'r') as file:
            extract_prompt = file.read()

        processed_change_llm = preprocess(change_llm_prompt, recursive=False, double_curly_brackets=False)
        llm, token_counter, input_cost, output_cost, model_name = llm_selector(strength, temperature)

        change_template = PromptTemplate.from_template(processed_change_llm)
        change_chain = change_template | llm | StrOutputParser()

        change_result = change_chain.invoke({
            "input_prompt": input_prompt,
            "input_code": input_code,
            "change_prompt": change_prompt
        })

        input_tokens = token_counter(processed_change_llm + input_prompt + input_code + change_prompt)
        output_tokens = token_counter(change_result)
        change_cost = (input_tokens * input_cost + output_tokens * output_cost) / 1_000_000

        console.print(f"[bold]Change LLM Output:[/bold]")
        console.print(change_result)
        console.print(f"Input tokens: {input_tokens}, Output tokens: {output_tokens}")
        console.print(f"Estimated cost: ${change_cost:.6f}")

        extract_template = PromptTemplate.from_template(extract_prompt)
        extract_chain = extract_template | llm | JsonOutputParser()

        extract_result = extract_chain.invoke({"llm_output": change_result})

        input_tokens = token_counter(extract_prompt + change_result)
        output_tokens = token_counter(str(extract_result))
        extract_cost = (input_tokens * input_cost + output_tokens * output_cost) / 1_000_000

        console.print(f"[bold]Extract Prompt Output:[/bold]")
        console.print(extract_result)
        console.print(f"Input tokens: {input_tokens}, Output tokens: {output_tokens}")
        console.print(f"Estimated cost: ${extract_cost:.6f}")

        if 'modified_prompt' not in extract_result:
            raise KeyError("'modified_prompt' key is missing from the extracted result")
        
        modified_prompt = extract_result['modified_prompt']
        console.print(Markdown(f"[bold]Modified Prompt:[/bold]\n\n{modified_prompt}"))

        total_cost = change_cost + extract_cost
        return modified_prompt, total_cost, model_name

    except FileNotFoundError as e:
        console.print(f"[bold red]Error: Prompt file not found.[/bold red]\n{str(e)}")
        raise Exception(f"Error: Prompt file not found. {str(e)}")
    except KeyError as e:
        console.print(f"[bold red]Error: Missing key in JSON output.[/bold red]\n{str(e)}")
        raise
    except Exception as e:
        console.print(f"[bold red]An unexpected error occurred:[/bold red]\n{str(e)}")
        raise