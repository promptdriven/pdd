import os
from typing import List, Dict, Tuple
from langchain_core.prompts import PromptTemplate
from langchain_core.output_parsers import JsonOutputParser
from langchain_core.pydantic_v1 import BaseModel, Field
from langchain_core.output_parsers import StrOutputParser
from .llm_selector import llm_selector


class Conflict(BaseModel):
    description: str = Field(description="A brief description of the conflict")
    explanation: str = Field(description="A detailed explanation of why this is a conflict")
    suggestion1: str = Field(description="A suggestion on how to modify prompt1 to resolve the conflict")
    suggestion2: str = Field(description="A suggestion on how to modify prompt2 to resolve the conflict")


class ConflictOutput(BaseModel):
    conflicts: List[Conflict] = Field(description="List of conflicts found in the prompts")


def conflicts_in_prompts(prompt1: str, prompt2: str, strength: float = 0.5, temperature: float = 0) -> Tuple[List[Dict[str, str]], float]:
    """
    Analyze conflicts between two prompts using Langchain LCEL.

    :param prompt1: The first prompt to analyze.
    :param prompt2: The second prompt to analyze.
    :param strength: The strength parameter for the LLM selector.
    :param temperature: The temperature parameter for the LLM selector.
    :return: A tuple containing a list of conflicts and the total cost of analysis.
    """
    # Step 1: Load prompts
    pdd_path = os.getenv('PDD_PATH')
    if not pdd_path:
        raise ValueError("PDD_PATH environment variable is not set")

    try:
        with open(f"{pdd_path}/prompts/conflict_LLM.prompt", "r") as f:
            conflict_prompt_template = f.read()

        with open(f"{pdd_path}/prompts/extract_conflict_LLM.prompt", "r") as f:
            extract_prompt_template = f.read()
    except FileNotFoundError as e:
        raise FileNotFoundError(f"Prompt file not found: {e}")

    # Step 2: Create Langchain LCEL template for conflict analysis
    conflict_prompt = PromptTemplate.from_template(conflict_prompt_template)

    # Step 3: Use llm_selector for the model
    llm, token_counter, input_cost, output_cost, model_name = llm_selector(strength, temperature)

    # Step 4: Run the prompts through the model
    conflict_chain = conflict_prompt | llm | StrOutputParser()

    # Calculate token count and cost for conflict analysis
    conflict_input = conflict_prompt.format(PROMPT1=prompt1, PROMPT2=prompt2)
    conflict_token_count = token_counter(conflict_input)
    conflict_cost = (conflict_token_count * input_cost) / 1_000_000

    print(f"Running conflict analysis using {model_name}...")
    print(f"Input tokens: {conflict_token_count}")
    print(f"Estimated cost: ${conflict_cost:.6f}")

    try:
        conflict_output = conflict_chain.invoke({"PROMPT1": prompt1, "PROMPT2": prompt2})
    except Exception as e:
        raise RuntimeError(f"Error during conflict analysis: {e}")

    # Step 5: Create Langchain LCEL template for extracting conflicts
    extract_prompt = PromptTemplate.from_template(extract_prompt_template)
    parser = JsonOutputParser(pydantic_object=ConflictOutput)

    extract_chain = extract_prompt | llm | parser

    # Calculate token count and cost for extraction
    extract_input = extract_prompt.format(llm_output=conflict_output)
    extract_token_count = token_counter(extract_input)
    extract_cost = (extract_token_count * input_cost) / 1_000_000

    print(f"\nExtracting conflicts from analysis...")
    print(f"Input tokens: {extract_token_count}")
    print(f"Estimated cost: ${extract_cost:.6f}")

    try:
        extract_output = extract_chain.invoke({"llm_output": conflict_output})
    except Exception as e:
        raise RuntimeError(f"Error during conflict extraction: {e}")

    # Step 6: Return the list of conflicts and total cost
    conflicts = extract_output.get("conflicts", [])
    total_cost = conflict_cost + extract_cost

    return conflicts, total_cost


# Example usage
if __name__ == "__main__":
    prompt1 = "Write a story about a brave knight."
    prompt2 = "Write a story about a peaceful farmer."
    conflicts, total_cost = conflicts_in_prompts(prompt1, prompt2)
    print(f"Conflicts: {conflicts}")
    print(f"Total cost: ${total_cost:.6f}")
