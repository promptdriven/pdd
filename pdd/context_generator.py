from typing import Tuple
from rich import print
from .load_prompt_template import load_prompt_template
from .llm_invoke import llm_invoke
from .unfinished_prompt import unfinished_prompt
from .continue_generation import continue_generation
from .postprocess import postprocess

def context_generator(
    code_module: str,
    prompt: str,
    language: str = "python",
    strength: float = 0.5,
    temperature: float = 0.0,
    verbose: bool = False
) -> Tuple[str, float, str]:
    """
    Generate a concise example demonstrating how to use a code module properly.

    Args:
        code_module (str): The code module to generate an example for.
        prompt (str): The prompt used to generate the code_module.
        language (str, optional): Programming language. Defaults to "python".
        strength (float, optional): LLM model strength (0-1). Defaults to 0.5.
        temperature (float, optional): LLM temperature (0-1). Defaults to 0.0.
        verbose (bool, optional): Print detailed information. Defaults to False.

    Returns:
        Tuple[str, float, str]: (example_code, total_cost, model_name)
    """
    try:
        # Input validation
        if not code_module or not prompt:
            raise ValueError("code_module and prompt must not be empty")
        if not 0 <= strength <= 1 or not 0 <= temperature <= 1:
            raise ValueError("strength and temperature must be between 0 and 1")

        total_cost = 0.0
        model_name = ""

        # Step 1: Load the example generator prompt template
        example_prompt = load_prompt_template("example_generator_LLM")
        if not example_prompt:
            raise ValueError("Failed to load example generator prompt template")

        if verbose:
            print("[blue]Generating example using prompt template...[/blue]")

        # Step 2: Generate initial example using llm_invoke
        input_json = {
            "code_module": code_module,
            "processed_prompt": prompt,
            "language": language
        }

        initial_response = llm_invoke(
            prompt=example_prompt,
            input_json=input_json,
            strength=strength,
            temperature=temperature,
            verbose=verbose
        )

        total_cost += initial_response['cost']
        model_name = initial_response['model_name']
        initial_output = initial_response['result']

        # Step 3: Check if generation is complete
        last_chunk = initial_output[-600:] if len(initial_output) > 600 else initial_output
        reasoning, is_finished, unfinished_cost, _ = unfinished_prompt(
            prompt_text=last_chunk,
            strength=0.5,
            temperature=0.0,
            verbose=verbose
        )
        total_cost += unfinished_cost

        if verbose:
            print(f"[yellow]Completion check: {is_finished}[/yellow]")
            print(f"[yellow]Reasoning: {reasoning}[/yellow]")

        final_output = ""
        if not is_finished:
            # Step 3a: Continue generation if incomplete
            if verbose:
                print("[blue]Continuing incomplete generation...[/blue]")
            
            continued_output, continue_cost, continue_model = continue_generation(
                formatted_input_prompt=example_prompt,
                llm_output=initial_output,
                strength=strength,
                temperature=temperature,
                verbose=verbose
            )
            total_cost += continue_cost
            model_name = continue_model
            final_output = continued_output
        else:
            # Step 3b: Postprocess if complete
            if verbose:
                print("[blue]Post-processing complete generation...[/blue]")
            
            final_output, postprocess_cost, _ = postprocess(
                initial_output,
                language,
                strength=0.8,
                temperature=temperature
            )
            total_cost += postprocess_cost

        return final_output, total_cost, model_name

    except Exception as e:
        print(f"[red]Error in context_generator: {str(e)}[/red]")
        raise
