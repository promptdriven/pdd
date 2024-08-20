import os
from rich.console import Console
from rich.markdown import Markdown
from preprocess import preprocess
from llm_selector import llm_selector
from postprocess import postprocess
from langchain_core.prompts import PromptTemplate
from langchain_core.output_parsers import StrOutputParser

console = Console()

def generate_test(prompt: str, code: str, strength: float, temperature: float, language: str) -> tuple[str, float]:
    """Generates unit test code from a given prompt and code snippet using a language model."""
    try:
        # Step 1: Load the prompt file
        pdd_path = os.getenv('PDD_PATH')
        with open(f'{pdd_path}/prompts/generate_test_LLM.prompt', 'r') as file:
            generate_test_prompt = file.read()
    except FileNotFoundError:
        console.print("[bold red]Prompt file not found.[/bold red]")
        return "", 0.0
    except Exception as e:
        console.print(f"[bold red]Error loading prompt file: {e}[/bold red]")
        return "", 0.0

    # Step 2: Preprocess the prompt
    processed_prompt = preprocess(generate_test_prompt, recursive=False, double_curly_brackets=False)

    # Step 3: Use llm_selector for the model
    llm, token_counter, input_cost, output_cost, model_name = llm_selector(strength, temperature)

    # Create Langchain LCEL template
    prompt_template = PromptTemplate.from_template(processed_prompt)
    chain = prompt_template | llm | StrOutputParser()

    # Step 4: Run inputs through the model
    input_tokens = token_counter(processed_prompt + prompt + code + language)
    input_cost_estimate = (input_tokens / 1_000_000) * input_cost

    console.print(f"[bold]Running test generator...[/bold]")
    console.print(f"Input tokens: {input_tokens}")
    console.print(f"Estimated input cost: ${input_cost_estimate:.6f}")

    try:
        result = chain.invoke({
            "prompt_that_generated_code": prompt,
            "code": code,
            "language": language
        })
    except Exception as e:
        console.print(f"[bold red]Error invoking model: {e}[/bold red]")
        return "", 0.0

    # Step 5: Pretty print the result
    console.print(Markdown(result))
    
    output_tokens = token_counter(result)
    output_cost_estimate = (output_tokens / 1_000_000) * output_cost
    console.print(f"Output tokens: {output_tokens}")
    console.print(f"Estimated output cost: ${output_cost_estimate:.6f}")

    # Step 6: Postprocess the result
    unit_test_code, postprocess_cost = postprocess(result, language, strength, temperature)
    
    # Calculate total cost
    total_cost = input_cost_estimate + output_cost_estimate + postprocess_cost
    console.print(f"Postprocess cost: ${postprocess_cost:.6f}")
    console.print(f"[bold]Total cost: ${total_cost:.6f}[/bold]")

    # Step 7: Return the unit test code and total cost
    return unit_test_code, total_cost