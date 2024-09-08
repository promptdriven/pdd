import os
from typing import List, Dict, Any, Tuple
from rich import print as rprint
from langchain_core.prompts import PromptTemplate
from langchain_core.output_parsers import JsonOutputParser, StrOutputParser
from langchain_core.pydantic_v1 import BaseModel, Field
from .llm_selector import llm_selector


class Conflict(BaseModel):
    description: str = Field(description="A brief description of the conflict")
    explanation: str = Field(description="A detailed explanation of why this is a conflict")
    suggestion1: str = Field(description="Instructions on how to modify prompt1 to resolve the conflict")
    suggestion2: str = Field(description="Instructions on how to modify prompt2 to resolve the conflict")


class ConflictOutput(BaseModel):
    conflicts: List[Conflict] = Field(description="List of conflicts found in the prompts")


def conflicts_in_prompts(prompt1: str, prompt2: str, strength: float = 0.5, temperature: float = 0) -> Tuple[List[Dict[str, str]], float, str]:
    """
    Analyzes two prompts for conflicts using a language model.

    Args:
        prompt1 (str): The first prompt to analyze.
        prompt2 (str): The second prompt to analyze.
        strength (float): The strength parameter for the language model.
        temperature (float): The temperature parameter for the language model.

    Returns:
        Tuple[List[Dict[str, str]], float, str]: A tuple containing a list of conflicts, the total cost, and the model name.
    """
    try:
        # Step 1: Load prompt files
        pdd_path = os.getenv('PDD_PATH')
        if not pdd_path:
            raise ValueError("PDD_PATH environment variable is not set")

        with open(f"{pdd_path}/prompts/conflict_LLM.prompt", "r") as f:
            conflict_prompt_template = f.read()

        with open(f"{pdd_path}/prompts/extract_conflict_LLM.prompt", "r") as f:
            extract_conflict_prompt_template = f.read()

        # Step 2 & 3: Create Langchain LCEL template and use llm_selector
        llm, token_counter, input_cost, output_cost, model_name = llm_selector(strength, temperature)

        conflict_prompt = PromptTemplate.from_template(conflict_prompt_template)

        # Step 4: Run the prompts through the model
        conflict_chain = conflict_prompt | llm | StrOutputParser()

        input_params = {"PROMPT1": prompt1, "PROMPT2": prompt2}
        input_tokens = token_counter(conflict_prompt.format(**input_params))
        input_cost_estimate = (input_tokens / 1_000_000) * input_cost

        rprint(f"[bold]Running conflict analysis...[/bold]")
        rprint(f"Input tokens: {input_tokens}")
        rprint(f"Estimated input cost: ${input_cost_estimate:.6f}")

        llm_output = conflict_chain.invoke(input_params)

        # Step 5: Extract conflicts using a separate LLM call
        extract_llm, extract_token_counter, extract_input_cost, extract_output_cost, _ = llm_selector(0.9, 0)

        parser = JsonOutputParser(pydantic_object=ConflictOutput)
        extract_prompt = PromptTemplate(
            template=extract_conflict_prompt_template,
            input_variables=["llm_output"],
            partial_variables={"format_instructions": parser.get_format_instructions()}
        )

        extract_chain = extract_prompt | extract_llm | parser

        extract_input_params = {"llm_output": llm_output}
        extract_input_tokens = extract_token_counter(extract_prompt.format(**extract_input_params))
        extract_input_cost_estimate = (extract_input_tokens / 1_000_000) * extract_input_cost

        rprint(f"[bold]Extracting conflicts...[/bold]")
        rprint(f"Input tokens: {extract_input_tokens}")
        rprint(f"Estimated input cost: ${extract_input_cost_estimate:.6f}")

        result = extract_chain.invoke(extract_input_params)

        # Calculate total cost
        output_tokens = token_counter(llm_output) + token_counter(str(result))
        output_cost_estimate = (output_tokens / 1_000_000) * output_cost
        total_cost = input_cost_estimate + output_cost_estimate + extract_input_cost_estimate

        # Step 6: Return the results
        return result.get('conflicts', []), total_cost, model_name
    except (ValueError, FileNotFoundError):
        raise
    except Exception as e:
        rprint(f"[bold red]Unexpected error: {str(e)}[/bold red]")
        return [], 0, ""
