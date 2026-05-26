import os
import sys
import json
from typing import Optional
from pydantic import BaseModel

# Import the llm_invoke function
from pdd.llm_invoke import llm_invoke, set_verbose_logging

# Enable verbose logging for the example to see token counts and costs
set_verbose_logging(True)

# Check for an API key to ensure the example can run
# We'll check for a common one, but llm_invoke handles missing keys interactively or via fallback
# For this non-interactive example, we require one to be set to avoid the prompt.
if not os.environ.get("OPENAI_API_KEY") and not os.environ.get("ANTHROPIC_API_KEY") and not os.environ.get("GEMINI_API_KEY"):
    print("No common API keys found (OPENAI_API_KEY, ANTHROPIC_API_KEY, GEMINI_API_KEY).")
    print("Please set at least one to run this example successfully.")
    sys.exit(0)

# Also force local execution for the example to avoid cloud auth requirements
os.environ["PDD_FORCE_LOCAL"] = "1"

def basic_text_generation():
    """
    Example 1: Basic text generation using a simple prompt and input data.
    Uses strength=0.5 (defaults to base model in CSV).
    """
    print("\n--- Example 1: Basic Text Generation ---")
    
    prompt_template = "Explain the concept of {concept} in one short sentence."
    input_data = {"concept": "recursion"}
    
    response = llm_invoke(
        prompt=prompt_template,
        input_json=input_data,
        strength=0.5,       # 0.5 targets the base model
        temperature=0.7,
        verbose=True
    )
    
    print(f"\nResult:\n{response['result']}")
    print(f"Cost: ${response['cost']:.6f}")
    print(f"Model Used: {response['model_name']}")

def structured_output_generation():
    """
    Example 2: Generating structured output enforcing a Pydantic schema.
    """
    print("\n--- Example 2: Structured Output (Pydantic) ---")
    
    class PersonInfo(BaseModel):
        name: str
        age: int
        profession: str
        hobbies: list[str]
        
    prompt_template = "Extract information about {person_name} from this text: {text}"
    input_data = {
        "person_name": "Alice",
        "text": "Alice is a 30 year old software engineer who loves hiking, reading, and painting."
    }
    
    response = llm_invoke(
        prompt=prompt_template,
        input_json=input_data,
        strength=0.8,       # Higher strength targets higher ELO models, better for structured output
        temperature=0.1,    # Low temperature for deterministic extraction
        output_pydantic=PersonInfo,
        verbose=True
    )
    
    print("\nResult (Pydantic Object):")
    if isinstance(response['result'], PersonInfo):
        print(json.dumps(response['result'].model_dump(), indent=2))
    else:
        print("Failed to parse into Pydantic object:", response['result'])
        
    print(f"Cost: ${response['cost']:.6f}")


def batch_processing():
    """
    Example 3: Processing multiple inputs in a single batch.
    Requires a list of dictionaries for input_json.
    """
    print("\n--- Example 3: Batch Processing ---")
    
    prompt_template = "Translate '{phrase}' to {language}."
    batch_inputs = [
        {"phrase": "Hello world", "language": "Spanish"},
        {"phrase": "Good morning", "language": "French"},
        {"phrase": "Thank you", "language": "German"}
    ]
    
    response = llm_invoke(
        prompt=prompt_template,
        input_json=batch_inputs,
        strength=0.2,       # Lower strength targets cheaper models for bulk tasks
        use_batch_mode=True,
        verbose=True
    )
    
    print("\nResults (List):")
    for i, res in enumerate(response['result']):
        print(f"Item {i+1}: {res}")
        
    print(f"Total Batch Cost: ${response['cost']:.6f}")


def main():
    print("Running llm_invoke examples...")
    basic_text_generation()
    structured_output_generation()
    batch_processing()
    print("\nExamples complete.")

if __name__ == "__main__":
    main()