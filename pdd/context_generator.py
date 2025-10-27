from rich import print
from .load_prompt_template import load_prompt_template
from .preprocess import preprocess
from .llm_invoke import llm_invoke
from .unfinished_prompt import unfinished_prompt
from .continue_generation import continue_generation
from .postprocess import postprocess
from . import EXTRACTION_STRENGTH, DEFAULT_TIME
from typing import Optional

def context_generator(
    code_module: str,
    prompt: str,
    language: str = "python",
    strength: float = 0.5,
    temperature: float = 0,
    time: Optional[float] = DEFAULT_TIME,
    verbose: bool = False,
    source_file_path: str = None,
    example_file_path: str = None,
    module_name: str = None,
) -> tuple:
    """
    Generates a concise example on how to use a given code module properly.

    Args:
        code_module (str): The code module to generate a concise example for.
        prompt (str): The prompt that was used to generate the code_module.
        language (str): The language of the code module. Default is "python".
        strength (float): The strength of the LLM model to use. Default is 0.5. Range is between 0 and 1.
        temperature (float): The temperature of the LLM model to use. Default is 0. Range is between 0 and 1.
        time (Optional[float], optional): Time allocation for the LLM. Defaults to DEFAULT_TIME.
        verbose (bool): Whether to print out the details of the function. Default is False.

    Returns:
        tuple: A tuple containing the example code, total cost, and model name.
    """
    # Step 0: Input validation
    if not code_module:
        if verbose:
            print("[red]Error: code_module is missing.[/red]")
        return None, 0.0, None

    if not prompt:
        if verbose:
            print("[red]Error: prompt is missing.[/red]")
        return None, 0.0, None


    if not (0 <= strength <= 1):
        if verbose:
            print(f"[red]Error: Invalid strength '{strength}'. Must be between 0 and 1.[/red]")
        return None, 0.0, None

    if not (0 <= temperature <= 1):
        if verbose:
            print(f"[red]Error: Invalid temperature '{temperature}'. Must be between 0 and 1.[/red]")
        return None, 0.0, None

    try:
        if verbose:
            print(f"[bold blue]Generating example for language: {language}[/bold blue]")

        # Step 1: Load and preprocess the 'example_generator_LLM' prompt template
        prompt_template = load_prompt_template("example_generator_LLM")
        if not prompt_template:
            raise ValueError("Failed to load the 'example_generator_LLM' prompt template.")

        processed_prompt_template = preprocess(prompt_template, recursive=False, double_curly_brackets=False)
        if verbose:
            print("[blue]Processed Prompt Template:[/blue]")
            print(processed_prompt_template)

        # Step 2: Preprocess the input prompt and run the code through the model using llm_invoke
        processed_prompt = preprocess(prompt, recursive=True, double_curly_brackets=True)
        if verbose:
            print("[blue]Processed Input Prompt:[/blue]")
            print(processed_prompt)

        llm_response = llm_invoke(
            prompt=processed_prompt_template,
            input_json={
                "code_module": code_module,
                "processed_prompt": processed_prompt,
                "language": language,
                "source_file_path": source_file_path or "",
                "example_file_path": example_file_path or "",
                "module_name": module_name or ""
            },
            strength=strength,
            temperature=temperature,
            time=time,
            verbose=verbose
        )

        # Step 3: Detect if the generation is incomplete using the unfinished_prompt function
        last_600_chars = llm_response['result'][-600:]
        try:
            reasoning, is_finished, unfinished_cost, unfinished_model = unfinished_prompt(
                prompt_text=last_600_chars,
                strength=0.5,
                temperature=temperature,
                time=time,
                language=language,
                verbose=verbose
            )
        except Exception as e:
            print(f"[red]Error in unfinished_prompt: {e}[/red]")
            is_finished = True  # Treat as finished if unfinished_prompt fails
            unfinished_cost = 0.0
            unfinished_model = None

        if not is_finished:
            if verbose:
                print("[yellow]Generation is incomplete. Continuing generation...[/yellow]")
            final_llm_output, continue_cost, continue_model = continue_generation(
                formatted_input_prompt=processed_prompt_template,
                llm_output=llm_response['result'],
                strength=strength,
                temperature=temperature,
                time=time,
                language=language,
                verbose=verbose
            )
            total_cost = llm_response['cost'] + unfinished_cost + continue_cost
            model_name = continue_model
        else:
            if verbose:
                print("[green]Generation is complete.[/green]")
            final_llm_output = llm_response['result']
            total_cost = llm_response['cost'] + unfinished_cost
            model_name = llm_response['model_name']

        # Step 4: Postprocess the model output result
        example_code, postprocess_cost, postprocess_model = postprocess(
            llm_output=final_llm_output,
            language=language,
            strength=EXTRACTION_STRENGTH,
            temperature=temperature,
            time=time,
            verbose=verbose
        )
        total_cost += postprocess_cost

        return example_code, total_cost, model_name

    except Exception as e:
        print(f"[red]An error occurred: {e}[/red]")
        return None, 0.0, None

# Example usage
if __name__ == "__main__":
    code_module = "numpy"
    prompt = "Generate a concise example of how to use numpy to create an array."
    example_code, total_cost, model_name = context_generator(code_module, prompt, verbose=True)
    if example_code:
        print("[bold green]Generated Example Code:[/bold green]")
        print(example_code)
        print(f"[bold blue]Total Cost: ${total_cost:.6f}[/bold blue]")
        print(f"[bold blue]Model Name: {model_name}[/bold blue]")
