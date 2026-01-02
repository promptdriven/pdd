from typing import Tuple, Optional
import logging
from rich.console import Console
from rich.syntax import Syntax
from pydantic import BaseModel, Field
from .load_prompt_template import load_prompt_template
from .preprocess import preprocess
from .llm_invoke import llm_invoke
from .unfinished_prompt import unfinished_prompt
from . import EXTRACTION_STRENGTH, DEFAULT_TIME

console = Console()
logger = logging.getLogger(__name__)

# Maximum number of generation loops to prevent infinite loops
MAX_GENERATION_LOOPS = 20

class TrimResultsStartOutput(BaseModel):
    explanation: str = Field(description="The explanation of how you determined what to cut out")
    code_block: str = Field(description="The trimmed code block from the start")

class TrimResultsOutput(BaseModel):
    explanation: str = Field(description="The explanation of the code block")
    trimmed_continued_generation: str = Field(description="The trimmed continuation of the generation")

def continue_generation(
    formatted_input_prompt: str,
    llm_output: str,
    strength: float,
    temperature: float,
    time: float = DEFAULT_TIME,
    language: Optional[str] = None,
    verbose: bool = False
) -> Tuple[str, float, str]:
    """
    Continue generating a prompt using a large language model until completion.
    
    Args:
        formatted_input_prompt (str): The input prompt with variables substituted.
        llm_output (str): Current output from the LLM to be checked and continued.
        strength (float): Strength parameter for the LLM model (0-1).
        temperature (float): Temperature parameter for the LLM model (0-1).
        time (float): Time budget for LLM calls.
        verbose (bool): Whether to print detailed information.
        
    Returns:
        Tuple[str, float, str]: Final LLM output, total cost, and model name.
    """
    try:
        # Validate inputs
        if not 0 <= strength <= 1:
            raise ValueError("Strength parameter must be between 0 and 1")
        if not 0 <= temperature <= 1:
            raise ValueError("Temperature parameter must be between 0 and 1")
        if not llm_output:
            raise ValueError("LLM output cannot be empty")

        # Step 1: Load prompt templates
        prompts = {
            'continue': load_prompt_template('continue_generation_LLM'),
            'trim_start': load_prompt_template('trim_results_start_LLM'),
            'trim': load_prompt_template('trim_results_LLM')
        }
        
        if not all(prompts.values()):
            raise ValueError("Failed to load one or more prompt templates")

        # Step 2: Preprocess prompts
        processed_prompts = {
            key: preprocess(prompt, recursive=True, double_curly_brackets=False)
            for key, prompt in prompts.items()
        }

        # Initialize tracking variables
        total_cost = 0.0
        model_name = ""
        loop_count = 0

        # Step 3: Trim start of output
        trim_start_response = llm_invoke(
            prompt=processed_prompts['trim_start'],
            input_json={"LLM_OUTPUT": llm_output},
            strength=EXTRACTION_STRENGTH,
            temperature=0,
            time=time,
            output_pydantic=TrimResultsStartOutput,
            verbose=verbose,
            language=language,
        )
        total_cost += trim_start_response['cost']
        code_block = trim_start_response['result'].code_block

        # Step 4: Continue generation loop
        while loop_count < MAX_GENERATION_LOOPS:
            loop_count += 1
            if verbose:
                console.print(f"[cyan]Generation loop {loop_count}[/cyan]")
            
            # Check for maximum loops reached
            if loop_count >= MAX_GENERATION_LOOPS:
                logger.warning(f"Reached maximum generation loops ({MAX_GENERATION_LOOPS}), terminating")
                console.print(f"[yellow]Warning: Reached maximum generation loops ({MAX_GENERATION_LOOPS}), terminating[/yellow]")
                break

            # Generate continuation
            continue_response = llm_invoke(
                prompt=processed_prompts['continue'],
                input_json={
                    "FORMATTED_INPUT_PROMPT": formatted_input_prompt,
                    "LLM_OUTPUT": code_block
                },
                strength=strength,
                temperature=temperature,
                time=time,
                verbose=verbose,
                language=language,
            )
            
            total_cost += continue_response['cost']
            model_name = continue_response['model_name']
            continue_result = continue_response['result']

            if verbose:
                try:
                    preview = (continue_result[:160] + '...') if isinstance(continue_result, str) and len(continue_result) > 160 else continue_result
                except Exception:
                    preview = "<non-str>"
                console.print(f"[blue]Continue model:[/blue] {model_name}")
                console.print(f"[blue]Continue preview:[/blue] {preview!r}")

            # If the model produced no continuation, avoid an endless loop
            if not isinstance(continue_result, str) or not continue_result.strip():
                logger.warning("Empty continuation received; stopping to avoid loop.")
                break

            # Build prospective new block and check completeness on the updated tail
            new_code_block = code_block + continue_result
            last_chunk = new_code_block[-600:] if len(new_code_block) > 600 else new_code_block
            reasoning, is_finished, check_cost, check_model = unfinished_prompt(
                prompt_text=last_chunk,
                strength=0.5,
                temperature=0,
                time=time,
                language=language,
                verbose=verbose
            )
            total_cost += check_cost

            if verbose:
                console.print(f"[magenta]Tail length:[/magenta] {len(last_chunk)}")
                # Show a safe, shortened representation of the tail
                try:
                    tail_preview = (last_chunk[-200:] if len(last_chunk) > 200 else last_chunk)
                except Exception:
                    tail_preview = "<unprintable tail>"
                console.print(f"[magenta]Tail preview (last 200 chars):[/magenta]\n{tail_preview}")
                console.print(f"[magenta]Unfinished check model:[/magenta] {check_model}")
                console.print(f"[magenta]is_finished:[/magenta] {is_finished}")
                console.print(f"[magenta]Reasoning:[/magenta] {reasoning}")

            if not is_finished:
                code_block = new_code_block
                # Continue to next iteration
            else:
                # Trim and append final continuation
                trim_response = llm_invoke(
                    prompt=processed_prompts['trim'],
                    input_json={
                        "CONTINUED_GENERATION": continue_result,
                        "GENERATED_RESULTS": code_block[-200:]
                    },
                    strength=EXTRACTION_STRENGTH,
                    temperature=0,
                    time=time,
                    output_pydantic=TrimResultsOutput,
                    verbose=verbose,
                    language=language,
                )
                total_cost += trim_response['cost']
                code_block += trim_response['result'].trimmed_continued_generation
                break

        if verbose:
            syntax = Syntax(code_block, "python", theme="monokai", line_numbers=True)
            console.print("[bold green]Final Generated Code:[/bold green]")
            console.print(syntax)

        return code_block, total_cost, model_name

    except Exception as e:
        console.print(f"[bold red]Error in continue_generation: {str(e)}[/bold red]")
        raise
