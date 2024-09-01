from typing import List, Dict, Any, Tuple
import os
import json
from rich.console import Console
from rich.markdown import Markdown
from .preprocess import preprocess
from .llm_selector import llm_selector
from langchain_core.prompts import PromptTemplate
from langchain_core.output_parsers import StrOutputParser, JsonOutputParser
from langchain_core.runnables import RunnablePassthrough

console = Console()

def detect_change(prompt_files: List[str], change_description: str, strength: float, temperature: float) -> Tuple[List[Dict[str, Any]], float, str]:
    """
    Analyze a list of prompt files and a change description to determine which prompts need to be changed.

    Args:
        prompt_files (List[str]): A list of strings, each containing the filename of a prompt that may need to be changed.
        change_description (str): A string that describes the changes that need to be analyzed and potentially applied to the prompts.
        strength (float): A float value representing the strength parameter for the LLM model.
        temperature (float): A float value representing the temperature parameter for the LLM model.

    Returns:
        Tuple[List[Dict[str, Any]], float, str]: A tuple containing:
            - changes_list: A list of JSON objects, each containing the name of a prompt that needs to be changed and detailed instructions on how to change it.
            - total_cost: A float value representing the total cost of running the function.
            - model_name: A string representing the name of the selected LLM model.
    """
    try:
        # Step 1: Load prompt files
        pdd_path = os.environ.get('PDD_PATH', '')
        with open(os.path.join(pdd_path, 'prompts/detect_change_LLM.prompt'), 'r') as f:
            detect_change_prompt = f.read()
        with open(os.path.join(pdd_path, 'prompts/extract_detect_change_LLM.prompt'), 'r') as f:
            extract_prompt = f.read()

        # Step 2: Preprocess the detect_change_LLM prompt
        processed_detect_change_prompt = preprocess(detect_change_prompt, recursive=False, double_curly_brackets=False)

        # Step 3: Create Langchain LCEL template for detect_change_LLM
        detect_change_template = PromptTemplate.from_template(processed_detect_change_prompt)

        # Step 4: Use llm_selector for LLM model and token counting
        llm, token_counter, input_cost, output_cost, model_name = llm_selector(strength, temperature)

        # Step 5: Run the prompt_files and change_description through the model
        prompt_list = [{"PROMPT_NAME": file, "PROMPT_DESCRIPTION": open(file, 'r').read()} for file in prompt_files]
        preprocessed_change_description = preprocess(change_description, recursive=False, double_curly_brackets=False)

        detect_change_chain = (
            {"PROMPT_LIST": lambda x: json.dumps(prompt_list), "CHANGE_DESCRIPTION": lambda x: preprocessed_change_description}
            | detect_change_template
            | llm
            | StrOutputParser()
        )

        llm_output = detect_change_chain.invoke({})
        
        input_tokens = token_counter(json.dumps(prompt_list) + preprocessed_change_description)
        output_tokens = token_counter(llm_output)
        detect_change_cost = (input_tokens * input_cost + output_tokens * output_cost) / 1_000_000

        console.print(f"[bold]Detect Change LLM Output:[/bold]")
        console.print(llm_output)
        console.print(f"Input Tokens: {input_tokens}, Output Tokens: {output_tokens}")
        console.print(f"Estimated Cost: ${detect_change_cost:.6f}")

        # Step 6: Create Langchain LCEL template for extract_detect_change_LLM
        extract_template = PromptTemplate.from_template(extract_prompt)
        extract_chain = (
            {"llm_output": lambda x: llm_output}
            | extract_template
            | llm
            | JsonOutputParser()
        )

        extract_output = extract_chain.invoke({})
        
        extract_input_tokens = token_counter(llm_output)
        extract_output_tokens = token_counter(json.dumps(extract_output))
        extract_cost = (extract_input_tokens * input_cost + extract_output_tokens * output_cost) / 1_000_000

        console.print(f"[bold]Extract LLM Output:[/bold]")
        console.print(json.dumps(extract_output, indent=2))
        console.print(f"Input Tokens: {extract_input_tokens}, Output Tokens: {extract_output_tokens}")
        console.print(f"Estimated Cost: ${extract_cost:.6f}")

        # Step 7: Extract changes_list and pretty print
        changes_list = extract_output.get('changes_list', [])
        console.print(Markdown("## Extracted Changes List"))
        for change in changes_list:
            console.print(Markdown(f"- **{change['prompt_name']}**: {change['change_instructions']}"))

        # Step 8: Return results
        total_cost = detect_change_cost + extract_cost
        return changes_list, total_cost, model_name

    except FileNotFoundError as e:
        console.print(f"[bold red]Error: Prompt file not found.[/bold red]")
        console.print(f"Details: {str(e)}")
        raise
    except json.JSONDecodeError as e:
        console.print(f"[bold red]Error: Invalid JSON in LLM output.[/bold red]")
        console.print(f"Details: {str(e)}")
        raise
    except Exception as e:
        console.print(f"[bold red]An unexpected error occurred.[/bold red]")
        console.print(f"Details: {str(e)}")
        raise

# Example usage
if __name__ == "__main__":
    prompt_files = ["prompt1.txt", "prompt2.txt"]
    change_description = "Update all prompts to use more formal language."
    strength = 0.7
    temperature = 0.5

    try:
        changes_list, total_cost, model_name = detect_change(prompt_files, change_description, strength, temperature)
        console.print(f"[bold green]Function completed successfully.[/bold green]")
        console.print(f"Total Cost: ${total_cost:.6f}")
        console.print(f"Model Used: {model_name}")
    except Exception as e:
        console.print(f"[bold red]Function failed to complete.[/bold red]")
        console.print(f"Error: {str(e)}")