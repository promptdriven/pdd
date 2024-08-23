import os
from rich.console import Console
from rich.markdown import Markdown
from langchain_core.prompts import PromptTemplate
from langchain_core.output_parsers import StrOutputParser
from preprocess import preprocess
from llm_selector import llm_selector
from postprocess import postprocess

console = Console()

def code_generator(prompt: str, language: str, strength: float, temperature: float = 0) -> tuple[str, float]:
    """
    Generate code from a prompt using Langchain and various processing steps.

    Args:
    prompt (str): The raw prompt to be processed.
    language (str): The target programming language.
    strength (float): The strength of the LLM model (0 to 1).
    temperature (float): The temperature of the LLM model. Default is 0.

    Returns:
    tuple[str, float]: A tuple containing the runnable code and the total cost.
    """
    # Step 1: Preprocess the raw prompt
    processed_prompt = preprocess(prompt, recursive=False, double_curly_brackets=True)
    console.print("[bold green]Preprocessed Prompt:[/bold green]")
    console.print(processed_prompt)

    # Step 2: Create Langchain LCEL template
    prompt_template = PromptTemplate.from_template(processed_prompt)

    # Step 3: Use llm_selector for the model
    llm, token_counter, input_cost, output_cost, model_name = llm_selector(strength, temperature)

    # Step 4: Run the prompt through the model
    chain = prompt_template | llm | StrOutputParser()
    
    input_tokens = token_counter(processed_prompt)
    input_cost_actual = (input_tokens / 1_000_000) * input_cost
    
    console.print(f"[bold yellow]Running prompt through model...[/bold yellow]")
    console.print(f"Input tokens: {input_tokens}")
    console.print(f"Estimated input cost: ${input_cost_actual:.6f}")

    result = chain.invoke({})

    # Step 5: Pretty print the result and calculate output cost
    console.print("[bold green]Model Output:[/bold green]")
    console.print(Markdown(result))

    output_tokens = token_counter(result)
    output_cost_actual = (output_tokens / 1_000_000) * output_cost
    
    console.print(f"Output tokens: {output_tokens}")
    console.print(f"Estimated output cost: ${output_cost_actual:.6f}")

    # Step 6: Postprocess the result
    runnable_code, postprocess_cost = postprocess(result, language, strength, temperature)
    
    total_cost = input_cost_actual + output_cost_actual + postprocess_cost
    
    console.print("[bold green]Postprocessed Code:[/bold green]")
    console.print(runnable_code)
    console.print(f"[bold cyan]Total cost: ${total_cost:.6f}[/bold cyan]")

    # Step 7: Return the runnable code and total cost
    return runnable_code, total_cost

# Example usage
if __name__ == "__main__":
    sample_prompt = """
    <prompt>
        Write a Python function that calculates the factorial of a number.
        <pdd>example.txt</pdd>
    </prompt>
    """
    
    runnable_code, total_cost = code_generator(sample_prompt, "python", 0.7, 0.2)
    console.print("[bold magenta]Final Runnable Code:[/bold magenta]")
    console.print(runnable_code)
    console.print(f"[bold magenta]Final Total Cost: ${total_cost:.6f}[/bold magenta]")