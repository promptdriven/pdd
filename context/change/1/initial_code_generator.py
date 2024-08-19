import tiktoken
from rich.console import Console
from rich.markdown import Markdown
from langchain_core.prompts import PromptTemplate
from langchain_core.output_parsers import StrOutputParser
from langchain.globals import set_llm_cache
from langchain_community.cache import SQLiteCache

from preprocess import preprocess
from llm_selector import llm_selector
from postprocess import postprocess

console = Console()

def code_generator(prompt: str, language: str, strength: float, temperature: float = 0) -> tuple[str, float]:
    """
    Generates code based on a given prompt using a language model.

    Args:
        prompt (str): The input prompt to generate code from.
        language (str): The programming language for the output code.
        strength (float): The strength parameter for model selection.
        temperature (float, optional): The temperature parameter for model selection. Defaults to 0.

    Returns:
        tuple[str, float]: A tuple containing the runnable code and the total cost of the operation.
    """
    try:
        # Step 1: Preprocess the raw prompt
        processed_prompt = preprocess(prompt, recursive=False, double_curly_brackets=True)
        
        # Step 2: Create Langchain LCEL template
        prompt_template = PromptTemplate.from_template(processed_prompt)
        
        # Step 3: Use llm_selector for the model
        llm, input_cost, output_cost = llm_selector(strength, temperature)
        
        # Set up SQLite cache
        set_llm_cache(SQLiteCache(database_path=".langchain.db"))
        
        # Step 4: Run the prompt through the model
        encoding = tiktoken.get_encoding("cl100k_base")
        input_tokens = len(encoding.encode(processed_prompt))
        input_cost_actual = (input_tokens / 1_000_000) * input_cost
        
        console.print(f"[bold]Running prompt through model...[/bold]")
        console.print(f"Input tokens: {input_tokens}")
        console.print(f"Estimated input cost: ${input_cost_actual:.6f}")
        
        chain = prompt_template | llm | StrOutputParser()
        result = chain.invoke({})
        
        # Step 5: Pretty print the result and calculate output cost
        console.print(Markdown(result))
        
        output_tokens = len(encoding.encode(result))
        output_cost_actual = (output_tokens / 1_000_000) * output_cost
        
        console.print(f"Output tokens: {output_tokens}")
        console.print(f"Estimated output cost: ${output_cost_actual:.6f}")
        
        # Step 6: Postprocess the result
        runnable_code, postprocess_cost = postprocess(result, language, strength, temperature)
        
        total_cost = input_cost_actual + output_cost_actual + postprocess_cost
        
        console.print(f"[bold]Total cost: ${total_cost:.6f}[/bold]")
        
        # Step 7: Return the runnable code and total cost
        return runnable_code, total_cost
    except Exception as e:
        console.print(f"[bold red]An error occurred: {e}[/bold red]")
        return "", 0.0