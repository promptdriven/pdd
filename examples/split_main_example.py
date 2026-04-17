"""
Example demonstrating usage of pdd.split_main.split_main.

split_main is a CLI wrapper that:
1. Reads input files (prompt, code, example) via construct_paths
2. Calls the split function to split a prompt into sub_prompt and modified_prompt
3. Saves the results to output files
4. Returns (result_data_dict, total_cost, model_name)

Parameters:
    ctx (click.Context): Click context with obj dict containing:
        - strength (float): LLM strength 0.0-1.0, default 0.5
        - temperature (float): LLM temperature, default 0.0
        - time (float|None): Reasoning time 0.0-1.0, or None
        - force (bool): Overwrite existing files without prompting
        - quiet (bool): Suppress non-essential output
        - context (str|None): Optional context directory override
    input_prompt_file (str): Path to the prompt file to split
    input_code_file (str): Path to code file generated from prompt
    example_code_file (str): Path to example code file
    output_sub (Optional[str]): Path for sub-prompt output, or None for default
    output_modified (Optional[str]): Path for modified prompt output, or None for default
    legacy (bool): When True, use old 2-LLM-call path. Default False.

Returns:
    Tuple of:
        - Dict[str, str] with keys: sub_prompt_content, modified_prompt_content,
          output_sub, output_modified
        - float: total cost of the operation
        - str: model name used
"""

import sys
import os

sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from unittest.mock import patch, MagicMock, mock_open
import click

from pdd.split_main import split_main


def main() -> None:
    """Run a demonstration of split_main with mocked dependencies."""

    # Create a mock Click context
    ctx = MagicMock(spec=click.Context)
    ctx.obj = {
        "strength": 0.7,
        "temperature": 0.1,
        "time": 0.25,
        "force": True,
        "quiet": False,
        "context": None,
    }

    # Mock return values
    mock_input_strings = {
        "input_prompt": "Create a function to calculate factorial.",
        "input_code": "def factorial(n):\n    return 1 if n <= 1 else n * factorial(n-1)",
        "example_code": "result = factorial(5)\nprint(result)",
    }
    mock_output_paths = {
        "output_sub": "/tmp/sub_prompt.prompt",
        "output_modified": "/tmp/modified_prompt.prompt",
    }
    mock_resolved_config = {}
    mock_language = "python"

    sub_prompt_content = "% Extract: factorial computation logic"
    modified_prompt_content = "% Modified: Use factorial from sub-module"
    mock_cost = 0.004523
    mock_model = "gpt-4"

    with patch("pdd.split_main.construct_paths") as mock_cp, \
         patch("pdd.split_main.split") as mock_split, \
         patch("builtins.open", mock_open()):

        mock_cp.return_value = (
            mock_resolved_config,
            mock_input_strings,
            mock_output_paths,
            mock_language,
        )
        mock_split.return_value = (
            (sub_prompt_content, modified_prompt_content),
            mock_cost,
            mock_model,
        )

        result_data, total_cost, model_name = split_main(
            ctx=ctx,
            input_prompt_file="prompts/my_module_python.prompt",
            input_code_file="src/my_module.py",
            example_code_file="examples/my_module_example.py",
            output_sub=None,
            output_modified=None,
            legacy=False,
        )

    print("=== split_main Example Output ===")
    print("")
    print("Result data keys:", sorted(result_data.keys()))
    print("Sub-prompt content:", repr(result_data["sub_prompt_content"]))
    print("Modified prompt content:", repr(result_data["modified_prompt_content"]))
    print("Output sub path:", result_data["output_sub"])
    print("Output modified path:", result_data["output_modified"])
    print("")
    print(f"Total cost: ${total_cost:.6f}")
    print(f"Model used: {model_name}")
    print("")
    print("Return type check:")
    print(f"  result_data is dict: {isinstance(result_data, dict)}")
    print(f"  total_cost is float: {isinstance(total_cost, float)}")
    print(f"  model_name is str: {isinstance(model_name, str)}")


if __name__ == "__main__":
    main()
