
"""
Example Usage of llm_invoke Module

This script demonstrates how to use the `llm_invoke` function from the `llm_invoke.py` module.
Ensure that the environment variables are set and the required packages are installed before running this example.

Directory Structure:
├── pdd/
│   ├── llm_invoke.py
│   └── data/
│       └── llm_model.csv
└── examples/
    └── example_usage.py
"""

import os
from pathlib import Path
import json

# Absolute path to the llm_invoke module
LLM_INVOKE_PATH = Path(__file__).parent.parent / 'pdd' / 'llm_invoke.py'
import sys

# Add the path to sys.path to allow importing
sys.path.append(str(LLM_INVOKE_PATH.parent))

from pdd.llm_invoke import llm_invoke  # Import the llm_invoke function

def main() -> None:
    """
    Main function to demonstrate the usage of llm_invoke.
    """
    # Define the prompt template
    prompt = """
    Provide a summary for the following article in JSON format:
    {article}
    """

    # Input JSON with variables for the prompt
    input_json = {
        "article": (
            "Artificial Intelligence (AI) is rapidly evolving and transforming various industries. "
            "From healthcare to finance, AI applications are enhancing efficiency and innovation."
        )
    }

    # Desired output JSON structure (optional)
    output_json = {
        "summary": "string"  # Specify the expected type
    }

    # Strength parameter (0.0 to 1.0)
    strength = 0.7  # Higher strength favors models with higher ELO scores

    # Temperature for the LLM
    temperature = 0.5  # Controls the randomness of the output

    # Verbose flag to enable detailed output
    verbose = True

    # Invoke the LLM
    result = llm_invoke(
        prompt=prompt,
        input_json=input_json,
        strength=strength,
        temperature=temperature,
        verbose=verbose,
        output_json=output_json
    )

    # Accessing the results
    summary = result.get("result")
    cost = result.get("cost")
    model_name = result.get("model_name")

    print("\n--- Invocation Results ---")
    print(f"Summary: {summary}")
    print(f"Cost: ${cost:.6f} per invocation")
    print(f"Model Used: {model_name}")

if __name__ == "__main__":
    main()
