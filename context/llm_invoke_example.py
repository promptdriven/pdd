import os
import sys
from pydantic import BaseModel

# Import the target module functions
from pdd.llm_invoke import llm_invoke, set_verbose_logging

"""
Example usage of the pdd.llm_invoke module.

This module provides a unified interface for calling Large Language Models (LLMs)
across different providers (OpenAI, Anthropic, Gemini, local models, etc.) with
built-in support for model selection, cost calculation, and structured outputs.

Inputs for llm_invoke:
    - prompt (str): A string template containing placeholders like {topic}.
    - input_json (dict or list): Values to format into the prompt.
    - strength (float): 0.0 to 1.0. 0.0 picks the cheapest model, 0.5 picks the base model, 1.0 picks the highest ELO model.
    - temperature (float): Randomness of the model (e.g., 0.1 for deterministic, 0.8 for creative).
    - verbose (bool): Whether to print debug and token usage logs.
    - output_pydantic (BaseModel): A Pydantic class to enforce structured JSON output.
    - time (float): 0.0 to 1.0 indicating reasoning effort or budget for models that support it.

Outputs of llm_invoke (Dict):
    - result (str or BaseModel): The raw text or parsed structured object returned by the model.
    - cost (float): The estimated cost of the API call in USD ($).
    - model_name (str): The exact name of the model that was successfully used.
    - thinking_output (str | None): Internal reasoning text if the model provides it.
    - finish_reason (str): Why the model stopped generating (e.g., 'stop').
    - attempted_models (list): Chronological list of models attempted during fallback.
"""

def main() -> None:
    # Check for a required environment variable (API key)
    # The exact key depends on the models configured in your project's llm_model.csv
    api_key = os.environ.get("OPENAI_API_KEY")
    if not api_key:
        print("OPENAI_API_KEY not set. Set it to run this example.")
        sys.exit(0)

    # Optionally enable verbose Python logging for the module
    set_verbose_logging(True)

    print("--- Example 1: Simple Text Generation ---")
    # Call the LLM with a simple prompt and dictionary input
    response = llm_invoke(
        prompt="Tell me a one sentence interesting fact about {topic}.",
        input_json={"topic": "space"},
        strength=0.5,       # Use the default base model
        temperature=0.7,    # Slightly creative
        verbose=True,
        time=0.0            # No extra reasoning time required
    )
    
    print(f"Raw Result: {response['result']}")
    print(f"Model used: {response['model_name']}")
    print(f"Estimated Cost (USD): ${response['cost']:.6f}")
    print(f"Attempted Models: {response['attempted_models']}")


    print("\n--- Example 2: Structured Output with Pydantic ---")
    # Define a Pydantic model to enforce the shape of the LLM's response
    class FactStructure(BaseModel):
        fact: str
        category: str
        confidence: float

    # Call the LLM requesting the output to match the Pydantic schema
    response_structured = llm_invoke(
        prompt="Provide a fact about {topic} and categorize it. Output JSON only.",
        input_json={"topic": "the ocean"},
        strength=0.8,       # Prefer a higher-capability model for structured tasks
        temperature=0.1,    # Low temperature for strict compliance
        output_pydantic=FactStructure,
        verbose=True
    )

    # The 'result' is automatically parsed into a FactStructure instance
    result_obj = response_structured['result']
    
    print(f"Parsed Fact: {result_obj.fact}")
    print(f"Parsed Category: {result_obj.category}")
    print(f"Parsed Confidence: {result_obj.confidence}")
    print(f"Estimated Cost (USD): ${response_structured['cost']:.6f}")

if __name__ == "__main__":
    main()