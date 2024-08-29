import os
from typing import Tuple
from rich.console import Console
from rich.markdown import Markdown
from langchain_core.prompts import PromptTemplate
from langchain_core.output_parsers import StrOutputParser, JsonOutputParser
from langchain_core.pydantic_v1 import BaseModel, Field

from pdd.preprocess import preprocess
from pdd.llm_selector import llm_selector
from pdd.unfinished_prompt import unfinished_prompt

# Setup cache to save money and increase speeds
from langchain_community.cache import SQLiteCache
from langchain.globals import set_llm_cache

set_llm_cache(SQLiteCache(database_path=".langchain.db"))

console = Console()

class TrimResultsStart(BaseModel):
    code_block: str = Field(description="The extracted code block from the LLM output")

class TrimResults(BaseModel):
    trimmed_continued_generation: str = Field(description="The trimmed continuation of the generated text")

def continue_generation(formatted_input_prompt: str, llm_output: str, strength: float, temperature: float) -> Tuple[str, float, str]:
    total_cost = 0.0
    pdd_path = os.getenv('PDD_PATH', '')
    
    # Step 1: Load prompts
    prompts = {}
    for prompt_name in ['continue_generation_LLM', 'trim_results_start_LLM', 'trim_results_LLM']:
        with open(os.path.join(pdd_path, 'prompts', f'{prompt_name}.prompt'), 'r') as f:
            prompts[prompt_name] = f.read()
    
    # Step 2: Preprocess prompts
    processed_prompts = {name: preprocess(prompt, True, False) for name, prompt in prompts.items()}
    
    # Step 3: Create Langchain LCEL templates
    continue_template = PromptTemplate.from_template(processed_prompts['continue_generation_LLM'])
    trim_start_template = PromptTemplate.from_template(processed_prompts['trim_results_start_LLM'])
    trim_results_template = PromptTemplate.from_template(processed_prompts['trim_results_LLM'])
    
    # Step 4: Use llm_selector
    llm, token_counter, input_cost, output_cost, model_name = llm_selector(strength, temperature)
    llm_high, token_counter_high, input_cost_high, output_cost_high, _ = llm_selector(0.9, 0)
    
    # Create chains
    continue_chain = continue_template | llm | StrOutputParser()
    trim_start_chain = trim_start_template | llm_high | JsonOutputParser(pydantic_object=TrimResultsStart)
    trim_results_chain = trim_results_template | llm_high | JsonOutputParser(pydantic_object=TrimResults)
    
    # Step 5: Extract code_block
    trim_start_input = {"LLM_OUTPUT": llm_output}
    trim_start_result = trim_start_chain.invoke(trim_start_input)
    code_block = trim_start_result.get('code_block', '')
    
    # Calculate and add cost
    trim_start_tokens = token_counter_high(str(trim_start_input)) + token_counter_high(str(trim_start_result))
    trim_start_cost = (trim_start_tokens / 1e6) * (input_cost_high + output_cost_high)
    total_cost += trim_start_cost
    console.print(f"Trim Start Cost: ${trim_start_cost:.6f}")
    
    i = 0
    
    # Step 6: Run continue_generation
    while True:
        print(f"Generation {i}")
        i += 1

        continue_input = {
            "FORMATTED_INPUT_PROMPT": formatted_input_prompt,
            "LLM_OUTPUT": code_block
        }
        continued_generation = continue_chain.invoke(continue_input)
        console.print(Markdown(continued_generation))
        
        # Calculate and add cost
        continue_tokens = token_counter(str(continue_input)) + token_counter(continued_generation)
        continue_cost = (continue_tokens / 1e6) * (input_cost + output_cost)
        total_cost += continue_cost
        console.print(f"Continue Generation Cost: ${continue_cost:.6f}")
        
        # Step 7: Check if generation is complete
        reasoning, is_finished, unfinished_cost, _ = unfinished_prompt(continued_generation[-200:], 0.9, 0)
        total_cost += unfinished_cost
        console.print(f"Unfinished Prompt Cost: ${unfinished_cost:.6f}")
        
        # Step 8: Trim results
        trim_results_input = {
            "CONTINUED_GENERATION": continued_generation,
            "GENERATED_RESULTS": code_block[-200:]
        }
        trim_results = trim_results_chain.invoke(trim_results_input)
        trimmed_continued_generation = trim_results.get('trimmed_continued_generation', '')
        
        # Calculate and add cost
        trim_results_tokens = token_counter_high(str(trim_results_input)) + token_counter_high(str(trim_results))
        trim_results_cost = (trim_results_tokens / 1e6) * (input_cost_high + output_cost_high)
        total_cost += trim_results_cost
        console.print(f"Trim Results Cost: ${trim_results_cost:.6f}")
        
        # Step 9: Append and check completeness
        code_block += trimmed_continued_generation
        if is_finished:
            break
    
    # Step 10: Pretty print final output
    console.print(Markdown(code_block))
    console.print(f"Total tokens: {token_counter(code_block)}")
    console.print(f"Total cost: ${total_cost:.6f}")
    
    # Step 11: Return results
    return code_block, total_cost, model_name