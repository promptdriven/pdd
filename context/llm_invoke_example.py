import os
import sys
from pydantic import BaseModel

# Import the llm_invoke function and logging utility from the pdd package
from pdd.llm_invoke import llm_invoke, set_quiet_logging


def main():
    """
    Demonstrate the usage of llm_invoke for basic generation, 
    structured output, and batch processing.
    """
    # Check for required API key before attempting LLM calls.
    # The specific key required depends on your PDD_MODEL_DEFAULT or local llm_model.csv
    api_key = os.environ.get("OPENAI_API_KEY")
    if not api_key:
        print("OPENAI_API_KEY not set. Set it to run this example.")
        sys.exit(0)

    # Optionally suppress noisy logs from LiteLLM
    set_quiet_logging()

    print("--- Example 1: Basic Text Generation ---")
    # Uses string formatting based on input_json dictionary
    response = llm_invoke(
        prompt="Write a one-sentence fun fact about {topic}.",
        input_json={"topic": "space"},
        strength=0.5,       # 0.0 = cheapest, 0.5 = base model, 1.0 = highest ELO
        temperature=0.7,    # Creativity parameter
        verbose=False
    )
    
    print(f"Result: {response.get('result')}")
    print(f"Model Used: {response.get('model_name')}")
    print(f"Cost: ${response.get('cost', 0):.6f}")


    print("\n--- Example 2: Structured Output (Pydantic) ---")
    # Define a Pydantic model for the expected output structure
    class AnimalFact(BaseModel):
        animal_name: str
        lifespan_years: int
        is_mammal: bool

    # The LLM will be instructed to return a JSON matching this schema
    response_structured = llm_invoke(
        prompt="Give me a fact about a {animal}.",
        input_json={"animal": "kangaroo"},
        strength=0.5,
        temperature=0.1,    # Lower temperature for structured data is recommended
        output_pydantic=AnimalFact
    )

    result_obj = response_structured.get('result')
    if isinstance(result_obj, AnimalFact):
        print(f"Name: {result_obj.animal_name}")
        print(f"Lifespan: {result_obj.lifespan_years} years")
        print(f"Mammal: {result_obj.is_mammal}")
    else:
        print("Failed to parse into Pydantic model:", result_obj)


    print("\n--- Example 3: Batch Processing ---")
    # Pass a list of dictionaries to process multiple prompts concurrently
    batch_inputs = [
        {"word": "happy"},
        {"word": "sad"},
        {"word": "angry"}
    ]
    
    response_batch = llm_invoke(
        prompt="What is a common synonym for {word}? Reply with just one word.",
        input_json=batch_inputs,
        use_batch_mode=True,
        strength=0.1,       # Opt for a cheaper/faster model for bulk tasks
        temperature=0.3
    )
    
    print("Batch Results (list of strings):")
    for idx, res in enumerate(response_batch.get('result', [])):
        print(f"  Input '{batch_inputs[idx]['word']}': {res.strip()}")


if __name__ == "__main__":
    main()