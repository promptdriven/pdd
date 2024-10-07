import os
from typing import Tuple
from rich.console import Console
from rich.panel import Panel
from langchain_core.prompts import PromptTemplate
from langchain_core.output_parsers import JsonOutputParser
from pydantic import BaseModel, Field
from .preprocess import preprocess
from .llm_selector import llm_selector
from fuzzywuzzy import process
import json

console = Console()

class TraceOutput(BaseModel):
    prompt_line: str = Field(description="The equivalent line in the prompt file")

def trace(code_file: str, code_line: int, prompt_file: str, strength: float = 0.5, temperature: float = 0) -> Tuple[int, float, str]:
    """
    Trace the line number in the prompt file corresponding to the code line in the code file.

    Args:
    code_file (str): The text of the code file.
    code_line (int): The line number in the code file.
    prompt_file (str): The text of the .prompt file.
    strength (float): The strength of the LLM model to use. Default is 0.5.
    temperature (float): The temperature of the LLM model to use. Default is 0.

    Returns:
    Tuple[int, float, str]: A tuple containing the prompt line number, total cost, and model name.
    """
    try:
        # Step 1: Load prompt files
        pdd_path = os.getenv('PDD_PATH')
        if not pdd_path:
            raise ValueError("PDD_PATH environment variable is not set")

        trace_prompt_path = f"{pdd_path}/prompts/trace_LLM.prompt"
        extract_prompt_path = f"{pdd_path}/prompts/extract_promptline_LLM.prompt"

        try:
            with open(trace_prompt_path, "r") as f:
                trace_prompt = f.read()
        except FileNotFoundError:
            raise FileNotFoundError(f"No such file: {trace_prompt_path}")

        try:
            with open(extract_prompt_path, "r") as f:
                extract_prompt = f.read()
        except FileNotFoundError:
            raise FileNotFoundError(f"No such file: {extract_prompt_path}")

        # Step 2: Find the substring of the code_file that matches the code_line
        code_lines = code_file.splitlines()
        if code_line < 1 or code_line > len(code_lines):
            raise ValueError(f"Invalid code_line: {code_line}. File has {len(code_lines)} lines.")
        code_str = code_lines[code_line - 1]

        # Step 3-6: Process trace_LLM prompt and invoke the model
        preprocessed_trace_prompt = preprocess(trace_prompt, recursive=False, double_curly_brackets=False)
        trace_template = PromptTemplate.from_template(preprocessed_trace_prompt)
        llm, token_counter, input_cost, output_cost, model_name = llm_selector(strength, temperature)

        trace_chain = trace_template | llm

        trace_input = {
            "CODE_FILE": code_file,
            "CODE_STR": code_str,
            "PROMPT_FILE": prompt_file
        }

        token_count = token_counter(str(trace_input))
        estimated_cost = (input_cost + output_cost) * token_count / 1_000_000

        console.print(Panel(f"Running trace LLM with {token_count} tokens. Estimated cost: ${estimated_cost:.6f}"))

        llm_output = trace_chain.invoke(trace_input)

        # Step 7-10: Process extract_promptline_LLM prompt and invoke the model
        preprocessed_extract_prompt = preprocess(extract_prompt, recursive=False, double_curly_brackets=False)
        extract_template = PromptTemplate.from_template(preprocessed_extract_prompt)
        # llm, token_counter, input_cost, output_cost, _ = llm_selector(.5, temperature)
        parser = JsonOutputParser(pydantic_object=TraceOutput)
        extract_chain = extract_template | llm | parser

        extract_input = {"llm_output": llm_output}

        token_count = token_counter(str(extract_input))
        estimated_cost += (input_cost + output_cost) * token_count / 1_000_000

        console.print(Panel(f"Running extract LLM with {token_count} tokens. Estimated cost: ${estimated_cost:.6f}"))

        try:
            result = extract_chain.invoke(extract_input)
            console.print(f"LLM output: {result}")
            if isinstance(result, str):
                result_dict = json.loads(result)
                result = TraceOutput(**result_dict)
        except json.JSONDecodeError as e:
            console.print(f"[bold red]Error: Failed to parse JSON - {e}[/bold red]")
            raise
        except Exception as e:
            console.print(f"[bold red]Error: Failed to create TraceOutput object - {e}[/bold red]")
            raise

        # Step 11: Find the line of the prompt_file that matches the prompt_line
        prompt_lines = prompt_file.splitlines()
        best_match = process.extractOne(result['prompt_line'], prompt_lines)
        if best_match is None:
            raise ValueError("Could not find a matching line in the prompt file")
        prompt_line = prompt_lines.index(best_match[0]) + 1

        # Step 12: Return the results
        return prompt_line, estimated_cost, model_name

    except FileNotFoundError as e:
        console.print(f"[bold red]Error: File not found - {e}[/bold red]")
        raise
    except ValueError as e:
        console.print(f"[bold red]Error: {e}[/bold red]")
        raise
    except json.JSONDecodeError as e:
        console.print(f"[bold red]Error: Failed to parse JSON - {e}[/bold red]")
        raise
    except Exception as e:
        console.print(f"[bold red]An unexpected error occurred: {e}[/bold red]")
        raise
