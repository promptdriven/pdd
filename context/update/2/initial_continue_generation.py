import os
from typing import Tuple
from rich.console import Console
from rich.markdown import Markdown
from langchain_core.prompts import PromptTemplate
from langchain_core.output_parsers import StrOutputParser, JsonOutputParser
from langchain_core.pydantic_v1 import BaseModel, Field

from .preprocess import preprocess
from .llm_selector import llm_selector
from .unfinished_prompt import unfinished_prompt

console = Console()

class TrimResultsOutput(BaseModel):
    code_block: str = Field(description="The extracted code block")

class TrimResultsContinuedOutput(BaseModel):
    trimmed_continued_generation: str = Field(description="The trimmed continued generation")

def continue_generation(formatted_input_prompt: str, llm_output: str, strength: float, temperature: float) -> Tuple[str, float, str]:
    # Step 1: Load prompts
    pdd_path = os.getenv('PDD_PATH')
    if not pdd_path:
        raise ValueError("PDD_PATH environment variable is not set")

    prompts = {}
    for prompt_name in ['continue_generation_LLM', 'trim_results_start_LLM', 'trim_results_LLM']:
        with open(f"{pdd_path}/prompts/{prompt_name}.prompt", 'r') as file:
            prompts[prompt_name] = file.read()

    # Step 2: Preprocess prompts
    for prompt_name in prompts:
        prompts[prompt_name] = preprocess(prompts[prompt_name], recursive=True, double_curly_brackets=False)

    # Step 3: Create Langchain LCEL templates
    continue_generation_template = PromptTemplate.from_template(prompts['continue_generation_LLM'])
    trim_results_start_template = PromptTemplate.from_template(prompts['trim_results_start_LLM'])
    trim_results_template = PromptTemplate.from_template(prompts['trim_results_LLM'])

    # Step 4: Use llm_selector for models
    llm, token_counter, input_cost, output_cost, model_name = llm_selector(strength, temperature)
    llm_trim, _, _, _, _ = llm_selector(0.5, 0)

    continue_generation_chain = continue_generation_template | llm | StrOutputParser()
    trim_results_start_chain = trim_results_start_template | llm_trim | JsonOutputParser(pydantic_object=TrimResultsOutput)
    trim_results_chain = trim_results_template | llm_trim | JsonOutputParser(pydantic_object=TrimResultsContinuedOutput)

    total_cost = 0

    # Step 5: Extract code_block
    trim_start_result = trim_results_start_chain.invoke({"LLM_OUTPUT": llm_output})
    code_block = trim_start_result.get('code_block', '')

    input_tokens = token_counter(llm_output)
    output_tokens = token_counter(code_block)
    trim_start_cost = (input_tokens * input_cost + output_tokens * output_cost) / 1_000_000
    total_cost += trim_start_cost
    console.print(f"Trim start cost: ${trim_start_cost:.6f}")

    # Step 6: Run continue_generation
    loop_count = 0
    while True:
        loop_count += 1
        continue_result = continue_generation_chain.invoke({
            "FORMATTED_INPUT_PROMPT": formatted_input_prompt,
            "LLM_OUTPUT": code_block
        })

        input_tokens = token_counter(formatted_input_prompt + code_block)
        output_tokens = token_counter(continue_result)
        continue_cost = (input_tokens * input_cost + output_tokens * output_cost) / 1_000_000
        total_cost += continue_cost
        console.print(f"Continue generation cost (loop {loop_count}): ${continue_cost:.6f}")

        # Step 7: Check if generation is complete
        last_200_chars = continue_result[-200:]
        reasoning, is_finished, unfinished_cost, _ = unfinished_prompt(last_200_chars, 0.5, 0)
        total_cost += unfinished_cost
        console.print(f"Unfinished prompt cost: ${unfinished_cost:.6f}")

        if is_finished:
            # Step 7b: Trim results
            trim_result = trim_results_chain.invoke({
                "CONTINUED_GENERATION": continue_result,
                "GENERATED_RESULTS": code_block
            })
            trimmed_continued_generation = trim_result.get('trimmed_continued_generation', '')
            code_block += trimmed_continued_generation

            input_tokens = token_counter(continue_result + code_block)
            output_tokens = token_counter(trimmed_continued_generation)
            trim_cost = (input_tokens * input_cost + output_tokens * output_cost) / 1_000_000
            total_cost += trim_cost
            console.print(f"Trim results cost: ${trim_cost:.6f}")

            break
        else:
            # Step 7a: Continue generation
            code_block = continue_result
            console.print(f"Generation incomplete. Continuing... (Loop count: {loop_count})")

    # Step 8: Pretty print the final output
    console.print(Markdown(f"```python\n{code_block}\n```"))
    console.print(f"Total tokens: {token_counter(code_block)}")
    console.print(f"Total cost: ${total_cost:.6f}")

    # Step 9: Return results
    return code_block, total_cost, model_name