import os
from typing import List, Dict, Any, Tuple
from rich import print as rprint
from langchain_core.prompts import PromptTemplate
from langchain_core.output_parsers import StrOutputParser, JsonOutputParser
from .llm_selector import llm_selector

def conflicts_in_prompts(prompt1: str, prompt2: str, strength: float = 0.5, temperature: float = 0) -> Tuple[List[Dict[str, Any]], float, str]:
    """
    Analyze conflicts between two prompts and suggest resolutions.

    Args:
    prompt1 (str): First prompt to compare.
    prompt2 (str): Second prompt to compare.
    strength (float): Strength of the LLM model to use. Default is 0.5.
    temperature (float): Temperature of the LLM model to use. Default is 0.

    Returns:
    Tuple[List[Dict[str, Any]], float, str]: A tuple containing:
        - changes_list: List of JSON objects with change instructions.
        - total_cost: Total cost of the model run.
        - model_name: Name of the selected LLM model.
    """
    try:
        # Step 1: Load prompt files
        pdd_path = os.getenv('PDD_PATH')
        if not pdd_path:
            raise ValueError("PDD_PATH environment variable is not set")

        with open(os.path.join(pdd_path, 'prompts', 'conflict_LLM.prompt'), 'r') as f:
            conflict_prompt_template = f.read()

        with open(os.path.join(pdd_path, 'prompts', 'extract_conflict_LLM.prompt'), 'r') as f:
            extract_prompt_template = f.read()

        # Step 2: Create Langchain LCEL template for conflict detection
        conflict_prompt = PromptTemplate.from_template(conflict_prompt_template)

        # Step 3: Use llm_selector for the model
        llm, token_counter, input_cost, output_cost, model_name = llm_selector(strength, temperature)

        # Step 4: Calculate and print token count and cost
        conflict_tokens = token_counter(conflict_prompt_template + prompt1 + prompt2)
        conflict_cost = (conflict_tokens / 1_000_000) * (input_cost + output_cost)
        rprint(f"[bold]Running conflict detection...[/bold]")
        rprint(f"Token count: {conflict_tokens}")
        rprint(f"Estimated cost: ${conflict_cost:.6f}")

        # Step 5: Run conflict detection
        conflict_chain = conflict_prompt | llm | StrOutputParser()
        conflict_output = conflict_chain.invoke({"PROMPT1": prompt1, "PROMPT2": prompt2})

        # Step 5b: Pretty print the output
        rprint("[bold]Conflict Detection Output:[/bold]")
        rprint(conflict_output)

        # Step 6: Create Langchain LCEL template for change extraction
        extract_llm, extract_token_counter, extract_input_cost, extract_output_cost, _ = llm_selector(0.8, temperature)
        extract_prompt = PromptTemplate.from_template(extract_prompt_template)
        
        # Step 6a and 6b: Calculate and print token count and cost for extraction
        extract_tokens = extract_token_counter(extract_prompt_template + conflict_output)
        extract_cost = (extract_tokens / 1_000_000) * (extract_input_cost + extract_output_cost)
        rprint(f"[bold]Extracting changes...[/bold]")
        rprint(f"Token count: {extract_tokens}")
        rprint(f"Estimated cost: ${extract_cost:.6f}")

        # Run extraction
        extract_chain = extract_prompt | extract_llm | JsonOutputParser()
        extract_output = extract_chain.invoke({"llm_output": conflict_output})

        # Step 6c: Extract changes_list
        changes_list = extract_output.get('changes_list', [])

        # Ensure changes_list is a list
        if not isinstance(changes_list, list):
            rprint(f"[bold yellow]Warning: changes_list is not a list. Actual value: {changes_list}[/bold yellow]")
            changes_list = []

        # Step 7: Calculate total cost and return results
        total_cost = conflict_cost + extract_cost
        return changes_list, total_cost, model_name

    except FileNotFoundError as e:
        rprint(f"[bold red]Error: Prompt file not found.[/bold red]")
        rprint(f"Details: {str(e)}")
        return [], 0.0, ""
    except ValueError as e:
        rprint(f"[bold red]Error: Invalid input or environment variable.[/bold red]")
        rprint(f"Details: {str(e)}")
        return [], 0.0, ""
    except Exception as e:
        rprint(f"[bold red]An unexpected error occurred.[/bold red]")
        rprint(f"Details: {str(e)}")
        return [], 0.0, ""
