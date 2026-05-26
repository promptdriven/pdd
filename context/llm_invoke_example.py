import os
import sys
from typing import Dict, Any
from pydantic import BaseModel

# Import the llm_invoke function from the module
from pdd.llm_invoke import llm_invoke


def main() -> None:
    """
    Example script demonstrating how to use the llm_invoke function.
    
    llm_invoke provides a unified interface to call LLMs via LiteLLM, handling:
    - Model selection (based on cost/ELO strength from a CSV)
    - Context window validation
    - Structured outputs (Pydantic / JSON Schema)
    - Cost calculation and attribution tracking
    """
    # Ensure we have an API key to run without interactive prompts.
    # For this example, we assume we want to use an OpenAI model.
    api_key = os.environ.get("OPENAI_API_KEY")
    if not api_key:
        print("OPENAI_API_KEY not set. Set it to run this example.")
        sys.exit(0)

    # Set environment variables to control behavior in a headless environment
    # PDD_FORCE=1 disables interactive prompts for missing API keys
    os.environ["PDD_FORCE"] = "1"
    # Set a default model that uses the checked API key
    os.environ["PDD_MODEL_DEFAULT"] = "openai/gpt-4o-mini"

    print("--- Example 1: Basic Text Generation ---")
    # llm_invoke automatically formats the prompt string with input_json
    basic_response = llm_invoke(
        prompt="Write a one-sentence greeting for {name}.",
        input_json={"name": "Alice"},
        temperature=0.7,
        strength=0.5,  # 0.5 uses the base model
        verbose=False
    )
    
    print(f"Model Used: {basic_response.get('model_name')}")
    print(f"Result: {basic_response.get('result')}")
    print(f"Estimated Cost: ${basic_response.get('cost'):.6f}")
    print(f"Finish Reason: {basic_response.get('finish_reason')}")


    print("\n--- Example 2: Structured Output (Pydantic) ---")
    # Define a Pydantic model for the desired output structure
    class CharacterInfo(BaseModel):
        name: str
        role: str
        level: int

    # Pass the Pydantic class to output_pydantic to enforce JSON schema validation
    structured_response = llm_invoke(
        prompt="Generate a random fantasy RPG character.",
        input_json={},
        output_pydantic=CharacterInfo,
        temperature=0.8,
        verbose=False
    )
    
    result_obj = structured_response.get('result')
    # result_obj will be an instantiated CharacterInfo object
    if hasattr(result_obj, "model_dump"):
        print(f"Structured Result: {result_obj.model_dump()}")
    else:
        print(f"Fallback/Raw Result: {result_obj}")


    print("\n--- Example 3: Using Direct Messages API ---")
    # You can bypass the prompt/input_json template system and provide messages directly
    messages = [
        {"role": "system", "content": "You are a calculator. Return ONLY the integer result."},
        {"role": "user", "content": "What is 15 + 27?"}
    ]
    
    msg_response = llm_invoke(
        messages=messages,
        temperature=0.0,
        time=0.0  # Disable reasoning effort for simple tasks
    )
    print(f"Calculation Result: {msg_response.get('result')}")


if __name__ == "__main__":
    main()