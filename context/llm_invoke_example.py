"""
Example usage of the pdd.llm_invoke module.

This script demonstrates how to invoke Large Language Models using the PDD standard interface,
including basic generation, structured Pydantic outputs, and batch processing.
"""
import os
import sys
from pydantic import BaseModel

# Import the main invocation function and logging utility
from pdd.llm_invoke import llm_invoke, set_verbose_logging

def main():
    # Prevent interactive API key prompts in this headless example
    os.environ["PDD_FORCE"] = "1"
    
    # Require an API key to proceed with the example
    if not (os.environ.get("OPENAI_API_KEY") or os.environ.get("ANTHROPIC_API_KEY") or os.environ.get("GEMINI_API_KEY") or os.environ.get("GOOGLE_APPLICATION_CREDENTIALS")):
        print("No standard LLM API key found in the environment.")
        print("Please set OPENAI_API_KEY, ANTHROPIC_API_KEY, or GEMINI_API_KEY to run this example.")
        sys.exit(0)

    # Optional: Enable detailed internal logging for the module
    # set_verbose_logging(True)

    print("=== Example 1: Basic LLM Invocation ===")
    # Invoke an LLM using a prompt template and JSON input variables
    # 'strength' controls the model selection (0.0 = cheapest, 0.5 = base, 1.0 = most capable)
    response = llm_invoke(
        prompt="Tell me a very short joke about {topic}.",
        input_json={"topic": "programmers"},
        strength=0.5, 
        temperature=0.7,
        verbose=False
    )
    print(f"Result: {response['result']}")
    print(f"Model used: {response['model_name']}")
    print(f"Estimated Cost: ${response['cost']:.6f}\n")

    print("=== Example 2: Structured Output with Pydantic ===")
    # Define the desired output schema
    class JokeStructure(BaseModel):
        setup: str
        punchline: str
        rating: int

    # By passing output_pydantic, the module forces the LLM to return valid JSON matching the schema
    response_structured = llm_invoke(
        prompt="Create a joke about {topic}.",
        input_json={"topic": "data science"},
        strength=0.5,
        temperature=0.7,
        output_pydantic=JokeStructure
    )
    
    # The result is automatically parsed into the requested Pydantic model
    result_obj = response_structured['result']
    if isinstance(result_obj, JokeStructure):
        print(f"Setup: {result_obj.setup}")
        print(f"Punchline: {result_obj.punchline}")
        print(f"Rating: {result_obj.rating}/10\n")
    else:
        # Fallback string representation if parsing completely fails
        print(f"Result: {result_obj}\n")

    print("=== Example 3: Batch Mode ===")
    # Pass a list of dictionaries to process multiple inputs efficiently
    batch_input = [
        {"topic": "cats"},
        {"topic": "dogs"},
    ]
    response_batch = llm_invoke(
        prompt="Write a one-sentence fact about {topic}.",
        input_json=batch_input,
        strength=0.0, # Use cheapest model for batching
        temperature=0.1,
        use_batch_mode=True
    )
    
    # Result is a list of strings corresponding to the inputs
    results_list = response_batch['result']
    for i, res in enumerate(results_list):
        print(f"Input {i+1}: {res}")

if __name__ == "__main__":
    main()