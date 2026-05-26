"""
Example usage of the pdd.llm_invoke module.

This script demonstrates how to use the llm_invoke function for simple text generation,
structured output parsing via Pydantic, and direct message handling.
"""

import os
import sys
import json
from typing import Optional
from pydantic import BaseModel

# Import the target function from the module
from pdd.llm_invoke import llm_invoke, set_verbose_logging


# Define a Pydantic model for structured output demonstration
class JokeStructure(BaseModel):
    setup: str
    punchline: str
    rating: Optional[int] = None


def main():
    # Prevent llm_invoke from falling back to interactive input() for missing API keys
    os.environ["PDD_FORCE"] = "1"

    # Require an API key to run this headless example to avoid runtime errors
    api_key = os.environ.get("OPENAI_API_KEY")
    if not api_key:
        print("OPENAI_API_KEY not set. Set it to run this example.")
        sys.exit(0)

    # Turn on verbose logging to see the internal operations
    set_verbose_logging(True)

    print("\n--- Example 1: Simple Text Generation ---")
    # Uses prompt templates and input_json variables
    result1 = llm_invoke(
        prompt="Tell me a very short joke about {topic}.",
        input_json={"topic": "programmers"},
        strength=0.5,       # 0.5 requests the base model defined in your CSV
        temperature=0.7,
        verbose=True
    )
    print("\nResult Dictionary:")
    print(json.dumps({
        "cost_usd": result1.get("cost"),
        "model_name": result1.get("model_name"),
        "result": result1.get("result")
    }, indent=2))


    print("\n--- Example 2: Structured Output (Pydantic) ---")
    # Enforces the LLM to return JSON matching the JokeStructure Pydantic model
    result2 = llm_invoke(
        prompt="Create a joke about {topic}. Output ONLY a valid JSON object with 'setup' and 'punchline' keys.",
        input_json={"topic": "cloud computing"},
        strength=0.5,
        temperature=0.3,
        output_pydantic=JokeStructure,
        verbose=True
    )
    
    structured_result = result2.get("result")
    print("\nParsed Pydantic Object:")
    if isinstance(structured_result, JokeStructure):
        print(f"Setup: {structured_result.setup}")
        print(f"Punchline: {structured_result.punchline}")


    print("\n--- Example 3: Direct Messages Array ---")
    # Bypass prompt/input_json and send raw LiteLLM/OpenAI format messages
    custom_messages = [
        {"role": "system", "content": "You are a sarcastic AI."},
        {"role": "user", "content": "What is 2 + 2?"}
    ]
    result3 = llm_invoke(
        messages=custom_messages,
        strength=0.5,
        temperature=0.5,
        verbose=True
    )
    print("\nDirect Message Result:")
    print(result3.get("result"))


if __name__ == "__main__":
    main()