from pdd.unfinished_prompt import unfinished_prompt
from rich import print as rprint

# This script provides a concise example of how to use the `unfinished_prompt` function
# from the `pdd.unfinished_prompt` module.

# --- Pre-requisites for running this example: ---
# 1. The `pdd` Python package must be accessible. This means:
#    - It's installed in your Python environment (e.g., via pip if it's a package), OR
#    - The directory containing the `pdd` package is added to your PYTHONPATH.
#      For instance, if your project structure is:
#      my_project/
#      ├── pdd/  # The module's package
#      │   ├── __init__.py
#      │   ├── unfinished_prompt.py
#      │   ├── load_prompt_template.py
#      │   └── llm_invoke.py
#      └── examples/
#          └── run_this_example.py (this file)
#      You would typically run this script from the `my_project` directory
#      (e.g., `python examples/run_this_example.py`) after ensuring `my_project`
#      is in PYTHONPATH (e.g., `export PYTHONPATH=$PYTHONPATH:/path/to/my_project`).
#
# 2. The `pdd` package requires internal setup for its dependencies:
#    - A prompt template file named "unfinished_prompt_LLM" (e.g., "unfinished_prompt_LLM.txt")
#      must be present where `pdd.load_prompt_template` (used internally by `unfinished_prompt`)
#      can find it. This location is usually relative to the `pdd` package structure.
#    - The `pdd.llm_invoke` function (used internally) must be configured for access to an LLM.
#      This typically involves setting environment variables for API keys (e.g., `OPENAI_API_KEY`).
#
# This script should be saved outside the `pdd` package, for instance, in an
# `examples/` directory as shown above.
# To run: `python name_of_this_script.py` (adjust path as needed).

# --- Example Usage ---

# 1. Define the prompt text you want to analyze.
#    This example uses a prompt that is intentionally incomplete to demonstrate
#    the function's ability to detect incompleteness.
my_prompt_text = "Write a comprehensive guide on how to bake a sourdough bread, starting from creating a starter, then the kneading process, and finally"

rprint(f"[bold cyan]Analyzing prompt:[/bold cyan] \"{my_prompt_text}\"")

# 2. Call the `unfinished_prompt` function.
#    Review the function's docstring for detailed parameter information.
#    - `prompt_text` (str): The text of the prompt to analyze.
#    - `strength` (float, optional, 0.0-1.0, default=0.5): Influences the LLM's behavior or model choice.
#    - `temperature` (float, optional, 0.0-1.0, default=0.0): Controls the randomness of the LLM's output.
#    - `verbose` (bool, optional, default=False): If True, the function will print detailed internal logs.
#
#    The function returns a tuple: (reasoning, is_finished, total_cost, model_name)
#    - `reasoning` (str): The LLM's structured explanation for its completeness assessment.
#    - `is_finished` (bool): True if the prompt is considered complete, False otherwise.
#    - `total_cost` (float): The estimated cost of the LLM call. The unit (e.g., USD) depends on the LLM provider.
#    - `model_name` (str): The name of the LLM model that was used for the analysis.

# Example call with verbose output and custom strength/temperature settings.
reasoning_str, is_complete_flag, call_cost, llm_model = unfinished_prompt(
    prompt_text=my_prompt_text,
    strength=0.6,       # Example: using a specific strength value
    temperature=0.1,    # Example: using a low temperature for more deterministic reasoning
    verbose=True        # Set to True to see detailed logs from within the unfinished_prompt function
)

# 3. Print the results returned by the function.
rprint("\n[bold green]--- Analysis Results ---[/bold green]")
rprint(f"  [bold]Prompt Analyzed:[/bold] \"{my_prompt_text}\"")
rprint(f"  [bold]Is prompt complete?:[/bold] {'Yes, the LLM considers the prompt complete.' if is_complete_flag else 'No, the LLM suggests the prompt needs continuation.'}")
rprint(f"  [bold]LLM's Reasoning:[/bold]\n    {reasoning_str}") # Rich print will handle newlines in the reasoning string
rprint(f"  [bold]Cost of Analysis:[/bold] ${call_cost:.6f}") # Display cost, assuming USD. Adjust currency/format as needed.
rprint(f"  [bold]LLM Model Used:[/bold] {llm_model}")

# --- Example of calling with default parameters ---
# If you want to use the default strength (0.5), temperature (0.0), and verbose (False):
#
# default_prompt_text = "What is the capital of Canada?"
# rprint(f"\n[bold cyan]Analyzing prompt with default settings:[/bold cyan] \"{default_prompt_text}\"")
#
# reasoning_def, is_finished_def, cost_def, model_def = unfinished_prompt(
#     prompt_text=default_prompt_text
# )
#
# rprint("\n[bold green]--- Default Call Analysis Results ---[/bold green]")
# rprint(f"  [bold]Prompt Analyzed:[/bold] \"{default_prompt_text}\"")
# rprint(f"  [bold]Is prompt complete?:[/bold] {'Yes' if is_finished_def else 'No'}")
# rprint(f"  [bold]LLM's Reasoning:[/bold]\n    {reasoning_def}")
# rprint(f"  [bold]Cost of Analysis:[/bold] ${cost_def:.6f}")
# rprint(f"  [bold]LLM Model Used:[/bold] {model_def}")
