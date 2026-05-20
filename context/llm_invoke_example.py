import os
import sys
from typing import Optional
from pydantic import BaseModel

# Pin the runtime model BEFORE importing pdd.llm_invoke, because
# DEFAULT_BASE_MODEL is captured from PDD_MODEL_DEFAULT at import time.
os.environ["PDD_FORCE"] = "1"
os.environ["PDD_MODEL_DEFAULT"] = "openai/gpt-4o-mini"

# Import the llm_invoke function from the pdd module
from pdd.llm_invoke import llm_invoke, set_verbose_logging

def main():
    # We pinned PDD_MODEL_DEFAULT to an OpenAI model above, so OPENAI_API_KEY is required.
    api_key = os.environ.get("OPENAI_API_KEY")
    if not api_key:
        print("OPENAI_API_KEY not set. Set it to run this example.")
        sys.exit(0)

    print("--- Example 1: Basic Text Generation ---")
    # Example 1: Basic text generation using prompt and input_json
    # strength=0.5 means use the base model.
    response = llm_invoke(
        prompt="Tell me a short, one-sentence fact about {topic}.",
        input_json={"topic": "space"},
        strength=0.5,
        temperature=0.7,
        verbose=True
    )

    print(f"\nModel Used: {response['model_name']}")
    print(f"Cost: ${response['cost']:.6f}")
    print(f"Result: {response['result']}\n")

    print("--- Example 2: Structured Output using Pydantic ---")
    # Define a Pydantic model for structured output
    class SpaceFact(BaseModel):
        fact: str
        is_surprising: bool
        related_planet: Optional[str]

    # Example 2: Requesting structured output
    structured_response = llm_invoke(
        prompt="Provide a fact about {topic} and whether it is surprising.",
        input_json={"topic": "Mars"},
        strength=0.5,
        temperature=0.1,
        output_pydantic=SpaceFact,
        verbose=False
    )

    result_obj = structured_response['result']
    print(f"Structured Result Object: {type(result_obj)}")
    if isinstance(result_obj, SpaceFact):
        print(f"Fact: {result_obj.fact}")
        print(f"Surprising: {result_obj.is_surprising}")
        print(f"Planet: {result_obj.related_planet}\n")

    print("--- Example 3: Using direct messages format ---")
    # Example 3: Using LiteLLM/OpenAI raw message format instead of prompt/input_json
    messages = [
        {"role": "system", "content": "You are a helpful assistant."},
        {"role": "user", "content": "What is 2 + 2?"}
    ]

    msg_response = llm_invoke(
        messages=messages,
        strength=0.5,
        temperature=0.0
    )

    print(f"Result: {msg_response['result']}\n")

if __name__ == "__main__":
    main()
