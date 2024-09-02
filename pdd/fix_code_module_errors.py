import os
from pathlib import Path
from rich.console import Console
from rich.markdown import Markdown
from .llm_selector import llm_selector
from .preprocess import preprocess
from .postprocess import postprocess
from langchain.prompts import PromptTemplate
from langchain.schema.output_parser import StrOutputParser

console = Console()

def fix_code_module_errors(program: str, prompt: str, code: str, errors: str, strength: float, temperature: float = 0.0) -> tuple[str, float, str]:
    """
    Fix errors in a code module that caused a program to crash.

    Args:
        program (str): The program that was running the code module.
        prompt (str): The prompt that generated the code module.
        code (str): The code module that caused the crash.
        errors (str): The errors from the program run.
        strength (float): The strength of the LLM model to use (between 0 and 1).
        temperature (float): The temperature of the LLM model to use. Default is 0.

    Returns:
        tuple[str, float, str]: A tuple containing the fixed code, total cost, and model name.
    """
    try:
        # Step 1: Load the prompt file
        pdd_path = os.getenv('PDD_PATH')
        if not pdd_path:
            raise ValueError("PDD_PATH environment variable is not set")
        
        prompt_path = Path(pdd_path) / 'prompts' / 'fix_code_module_errors_LLM.prompt'
        with open(prompt_path, 'r') as file:
            fix_prompt_template = file.read()

        # Step 2: Create a Langchain LCEL template
        prompt_template = PromptTemplate.from_template(fix_prompt_template)

        # Step 3: Use llm_selector for the llm model
        llm, token_counter, input_cost, output_cost, model_name = llm_selector(strength, temperature)

        # Step 4: Run the code through the model using Langchain LCEL
        chain = prompt_template | llm | StrOutputParser()

        # Count tokens and calculate cost
        prompt_tokens = token_counter(prompt_template.format(program=program, prompt=prompt, code=code, errors=errors))
        prompt_cost = (prompt_tokens / 1_000_000) * input_cost

        console.print(f"[bold]Running fix_code_module_errors with {prompt_tokens} tokens[/bold]")
        console.print(f"Estimated prompt cost: ${prompt_cost:.6f}")

        # Invoke the chain
        result = chain.invoke({
            "program": program,
            "prompt": prompt,
            "code": code,
            "errors": errors
        })

        # Step 5: Pretty print the result
        console.print(Markdown(result))

        # Count result tokens and calculate cost
        result_tokens = token_counter(result)
        result_cost = (result_tokens / 1_000_000) * output_cost

        console.print(f"[bold]Result contains {result_tokens} tokens[/bold]")
        console.print(f"Estimated result cost: ${result_cost:.6f}")

        # Step 6: Extract the corrected code
        fixed_code, postprocess_cost = postprocess(result, "python", 0.9, temperature)

        # Step 7: Calculate and print total cost, return results
        total_cost = prompt_cost + result_cost + postprocess_cost
        console.print(f"[bold]Total cost of the run: ${total_cost:.6f}[/bold]")

        return fixed_code, total_cost, model_name

    except FileNotFoundError as e:
        console.print(f"[bold red]Error: Prompt file not found. {str(e)}[/bold red]")
        raise
    except ValueError as e:
        console.print(f"[bold red]Error: {str(e)}[/bold red]")
        raise
    except Exception as e:
        console.print(f"[bold red]An unexpected error occurred: {str(e)}[/bold red]")
        raise