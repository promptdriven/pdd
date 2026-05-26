import os
import sys
from typing import Any, Dict, Optional
from pydantic import BaseModel

# Import the target module
from pdd.llm_invoke import llm_invoke, set_verbose_logging

# ===========================================================================
# llm_invoke Example
# ===========================================================================
# The llm_invoke function is the central unified interface for interacting
# with LLM providers in PDD. It handles model selection (based on ELO/cost),
# fallback logic, structured output validation, token context window checks,
# and LiteLLM integration.
#
# Key Inputs:
#   prompt (str): Template string with {variable} placeholders.
#   input_json (Dict | List[Dict]): Variables for the template.
#   strength (float): 0.0 = cheapest, 0.5 = base model, 1.0 = highest ELO.
#   temperature (float): standard LLM temperature.
#   verbose (bool): Prints detailed internal steps if True.
#   output_pydantic (Type[BaseModel]): Enforces structured JSON output.
#   time (float): 0.0 to 1.0; dictates reasoning effort or budget.
#
# Key Outputs (Dict[str, Any]):
#   result: The generated text or validated Pydantic object.
#   cost (float): Estimated API cost in USD.
#   model_name (str): The actual model used after fallbacks.
#   attempted_models (List[str]): Audit trail of models tried.
# ===========================================================================

def main() -> None:
    """
    Main execution function to demonstrate the usage of llm_invoke
    with basic text generation and structured Pydantic output.
    """
    # Ensure we have an API key to avoid interactive prompts in the example
    api_key = os.environ.get("OPENAI_API_KEY")
    if not api_key:
        print("OPENAI_API_KEY not set. Set it to run this example.")
        sys.exit(0)

    # Prevent interactive prompts for missing multi-provider keys during the demo
    os.environ["PDD_FORCE"] = "1"

    # Optionally enable verbose logging
    set_verbose_logging(False)

    # Ensure output directory exists
    os.makedirs("./output", exist_ok=True)

    print("--- Example 1: Basic Text Generation ---")
    try:
        # We use strength=0.5 to target the base model configured in PDD
        response = llm_invoke(
            prompt="Explain the concept of {concept} in one short sentence.",
            input_json={"concept": "dependency injection"},
            strength=0.5,
            temperature=0.3,
            verbose=False
        )
        
        print(f"Result: {response.get('result')}")
        print(f"Model used: {response.get('model_name')}")
        print(f"Estimated cost: ${response.get('cost', 0):.6f}")
        print(f"Attempt trail: {response.get('attempted_models')}\n")
    except Exception as e:
        print(f"Error in Example 1: {e}")


    print("--- Example 2: Structured Output via Pydantic ---")
    # Define a Pydantic model for our expected output
    class CodeReview(BaseModel):
        issue_found: bool
        severity: str
        suggested_fix: str

    try:
        # Run the invocation requiring the output to match the Pydantic schema
        structured_response = llm_invoke(
            prompt="Review the following code: {code}",
            input_json={"code": "def add(a, b): return a - b"},
            strength=0.8,  # Request a smarter model (closer to 1.0 max ELO)
            temperature=0.0,
            output_pydantic=CodeReview,
            time=0.25,     # Allocate a moderate reasoning budget/effort
            verbose=False
        )

        result_obj = structured_response.get("result")
        print(f"Model used: {structured_response.get('model_name')}")
        print(f"Cost: ${structured_response.get('cost', 0):.6f}")
        
        if isinstance(result_obj, CodeReview):
            print("Successfully parsed structured output:")
            print(f"  Issue Found: {result_obj.issue_found}")
            print(f"  Severity: {result_obj.severity}")
            print(f"  Fix: {result_obj.suggested_fix}")
        else:
            print("Failed to extract structured data.")
    except Exception as e:
        print(f"Error in Example 2: {e}")

if __name__ == "__main__":
    main()