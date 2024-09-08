import os
from typing import List, Dict, Tuple
from rich.console import Console
from rich.markdown import Markdown
from .preprocess import preprocess
from .llm_selector import llm_selector
from langchain_core.prompts import PromptTemplate
from langchain_core.output_parsers import StrOutputParser, JsonOutputParser
import json

console = Console()

def custom_chain_executor(components, input_data):
    result = input_data
    for component in components:
        result = component.invoke(result)
    return result

def detect_change(prompt_files: List[str], change_description: str, strength: float, temperature: float) -> Tuple[List[Dict[str, str]], float, str]:
    """
    Analyze a list of prompt files and a change description to determine which prompts need to be changed.

    Args:
    prompt_files (List[str]): A list of strings, each containing the filename of a prompt that may need to be changed.
    change_description (str): A string that describes the changes that need to be analyzed and potentially applied to the prompts.
    strength (float): A float value representing the strength parameter for the LLM model.
    temperature (float): A float value representing the temperature parameter for the LLM model.

    Returns:
    Tuple[List[Dict[str, str]], float, str]: A tuple containing:
        - changes_list: A list of JSON objects, each containing the name of a prompt that needs to be changed and detailed instructions on how to change it.
        - total_cost: A float value representing the total cost of running the function.
        - model_name: A string representing the name of the selected LLM model.
    """
    try:
        # Step 1: Load prompt files
        pdd_path = os.getenv('PDD_PATH', '')
        with open(f'{pdd_path}/prompts/detect_change_LLM.prompt', 'r') as f:
            detect_change_prompt = f.read()
        with open(f'{pdd_path}/prompts/extract_detect_change_LLM.prompt', 'r') as f:
            extract_detect_change_prompt = f.read()

        # Step 2: Preprocess the detect_change_LLM prompt
        processed_detect_change_prompt = preprocess(detect_change_prompt, recursive=False, double_curly_brackets=False)

        # Step 3: Create Langchain LCEL template
        prompt_template = PromptTemplate.from_template(processed_detect_change_prompt)

        # Step 4: Use llm_selector
        llm, token_counter, input_cost, output_cost, model_name = llm_selector(strength, temperature)

        # Step 5: Run the prompt_files and change_description through the model
        prompt_list = []
        for file in prompt_files:
            with open(file, 'r') as f:
                prompt_content = f.read()
            prompt_list.append({
                'PROMPT_NAME': file,
                'PROMPT_DESCRIPTION': prompt_content
            })
        
        preprocessed_change_description = preprocess(change_description, recursive=False, double_curly_brackets=False)

        # Construct and run the custom chain
        chain_components = [prompt_template, llm, StrOutputParser()]
        llm_output = custom_chain_executor(chain_components, {
            'PROMPT_LIST': json.dumps(prompt_list),
            'CHANGE_DESCRIPTION': preprocessed_change_description
        })

        input_tokens = token_counter(json.dumps(prompt_list) + preprocessed_change_description)
        output_tokens = token_counter(llm_output)
        step5_cost = (input_tokens * input_cost + output_tokens * output_cost) / 1_000_000

        console.print(f"[bold]Step 5 Output:[/bold]")
        console.print(llm_output)
        console.print(f"Input tokens: {input_tokens}, Output tokens: {output_tokens}")
        console.print(f"Estimated cost: ${step5_cost:.6f}")

        # Step 6: Extract changes using the extract_detect_change_LLM prompt
        extract_llm, extract_token_counter, extract_input_cost, extract_output_cost, extract_model_name = llm_selector(0.9, temperature)
        
        extract_prompt_template = PromptTemplate.from_template(extract_detect_change_prompt)
        extract_chain_components = [extract_prompt_template, extract_llm, JsonOutputParser()]
        extract_output = custom_chain_executor(extract_chain_components, {'llm_output': llm_output})

        extract_input_tokens = extract_token_counter(llm_output)
        extract_output_tokens = extract_token_counter(json.dumps(extract_output))
        step6_cost = (extract_input_tokens * extract_input_cost + extract_output_tokens * extract_output_cost) / 1_000_000

        console.print(f"[bold]Step 6 Output:[/bold]")
        console.print(f"Input tokens: {extract_input_tokens}, Output tokens: {extract_output_tokens}")
        console.print(f"Estimated cost: ${step6_cost:.6f}")

        changes_list = extract_output.get('changes_list', [])

        # Step 7: Pretty print the extracted changes_list
        console.print(Markdown("## Extracted Changes List"))
        for change in changes_list:
            console.print(Markdown(f"### Prompt: {change['prompt_name']}"))
            console.print(Markdown(f"Change Instructions: {change['change_instructions']}"))

        # Step 8: Return the results
        total_cost = step5_cost + step6_cost
        return changes_list, total_cost, model_name

    except FileNotFoundError as e:
        console.print(f"[bold red]Error: File not found - {e}[/bold red]")
        return [], 0.0, ""
    except json.JSONDecodeError as e:
        console.print(f"[bold red]Error: Invalid JSON - {e}[/bold red]")
        return [], 0.0, ""
    except Exception as e:
        console.print(f"[bold red]Error: An unexpected error occurred - {e}[/bold red]")
        return [], 0.0, ""
