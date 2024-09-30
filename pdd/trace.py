import os
from typing import Tuple
from rich.console import Console
from langchain_core.prompts import PromptTemplate
from langchain_core.output_parsers import StrOutputParser
from .preprocess import preprocess
from .llm_selector import llm_selector
from fuzzywuzzy import process

console = Console()

def trace(code_file: str, code_line: int, prompt_file: str, strength: float = 0.5, temperature: float = 0) -> Tuple[int, float, str]:
    """
    Trace the line number in the prompt file that corresponds to the code line in the code file.

    Args:
        code_file (str): The text of the code file.
        code_line (int): The line number in the code file.
        prompt_file (str): The text of the .prompt file.
        strength (float): The strength of the LLM model to use. Default is 0.5.
        temperature (float): The temperature of the LLM model to use. Default is 0.

    Returns:
        Tuple[int, float, str]: A tuple containing:
            - prompt_line (int): The equivalent line number in the prompt file.
            - total_cost (float): The total cost of the function.
            - model_name (str): The name of the selected LLM model.

    Raises:
        FileNotFoundError: If the required prompt files are not found.
        ValueError: If there's an issue with the input parameters or LLM processing.
    """
    try:
        # Step 1: Load prompt files
        pdd_path = os.getenv('PDD_PATH')
        if not pdd_path:
            raise ValueError("PDD_PATH environment variable is not set")

        with open(os.path.join(pdd_path, 'prompts/trace_LLM.prompt'), 'r') as f:
            trace_prompt = f.read()
        with open(os.path.join(pdd_path, 'prompts/extract_promptline_LLM.prompt'), 'r') as f:
            extract_prompt = f.read()

        # Step 2: Find the substring of the code_file that matches the code_line
        code_lines = code_file.splitlines()
        if code_line < 1 or code_line > len(code_lines):
            raise ValueError(f"Invalid code_line: {code_line}. File has {len(code_lines)} lines.")
        code_str = code_lines[code_line - 1]

        # Step 3-6: Process trace_LLM prompt and invoke LLM
        trace_prompt_processed = preprocess(trace_prompt, recursive=False, double_curly_brackets=False)
        trace_template = PromptTemplate.from_template(trace_prompt_processed)
        llm, token_counter, input_cost, output_cost, model_name = llm_selector(strength, temperature)

        trace_chain = trace_template | llm | StrOutputParser()
        
        trace_input = {
            "CODE_FILE": code_file,
            "CODE_STR": code_str,
            "PROMPT_FILE": prompt_file
        }
        
        token_count = sum(token_counter(v) for v in trace_input.values())
        estimated_cost = (input_cost * token_count) / 1_000_000  # Convert to actual cost
        
        console.print(f"[bold]Running trace LLM (model: {model_name})[/bold]")
        console.print(f"Estimated input tokens: {token_count}")
        console.print(f"Estimated cost: ${estimated_cost:.6f}")

        llm_output = trace_chain.invoke(trace_input)

        # Step 7-10: Process extract_promptline_LLM prompt and invoke LLM
        extract_prompt_processed = preprocess(extract_prompt, recursive=False, double_curly_brackets=False)
        extract_template = PromptTemplate.from_template(extract_prompt_processed)
        
        llm, token_counter, input_cost, output_cost, model_name = llm_selector(0.5, temperature)

        extract_chain = extract_template | llm | StrOutputParser()
        
        extract_input = {"llm_output": llm_output}
        
        token_count = token_counter(llm_output)
        estimated_cost += (input_cost * token_count) / 1_000_000  # Add to total cost
        
        console.print(f"[bold]Running extract LLM (model: {model_name})[/bold]")
        console.print(f"Estimated input tokens: {token_count}")
        console.print(f"Estimated cost: ${estimated_cost:.6f}")

        extracted_line = extract_chain.invoke(extract_input)
        print(extracted_line)
        # Step 11: Find the matching line in prompt_file
        prompt_lines = prompt_file.splitlines()
        match = process.extractOne(extracted_line, prompt_lines)
        if match:
            prompt_line = prompt_lines.index(match[0]) + 1
        else:
            raise ValueError("Could not find a matching line in the prompt file")

        # Step 12: Return results
        total_cost = estimated_cost
        return prompt_line, total_cost, model_name

    except FileNotFoundError as e:
        console.print(f"[bold red]Error: Required prompt file not found.[/bold red]")
        console.print(f"Details: {str(e)}")
        raise
    except ValueError as e:
        console.print(f"[bold red]Error: {str(e)}[/bold red]")
        raise
    except Exception as e:
        console.print(f"[bold red]An unexpected error occurred: {str(e)}[/bold red]")
        raise
