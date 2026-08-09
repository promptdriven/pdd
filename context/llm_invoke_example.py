import os
import sys
import json
from typing import Optional
from pydantic import BaseModel

# Import the functions from the module
from pdd.llm_invoke import llm_invoke, set_verbose_logging, setup_file_logging

# Ensure the script runs non-interactively by forcing PDD to not prompt for keys
os.environ["PDD_FORCE"] = "1"

# Check for an API key to ensure the example can run successfully.
# The specific key depends on your configured default model in llm_model.csv.
api_key = os.environ.get("OPENAI_API_KEY")
if not api_key:
    print("OPENAI_API_KEY not set. Set it to run this example (or whichever key your default model requires).")
    sys.exit(0)

def main():
    # Setup output directory for any logs or outputs
    os.makedirs("./output", exist_ok=True)
    
    # 1. Configure logging
    setup_file_logging("./output/llm_invoke_example.log")
    set_verbose_logging(verbose=True)

    print("\n--- Example 1: Basic LLM Invocation ---")
    # We use a simple prompt and input_json mapping.
    # strength=0.5 requests the base model defined in the environment or CSV.
    response = llm_invoke(
        prompt="Translate the following text to French: {text}",
        input_json={"text": "Hello, how are you?"},
        strength=0.5,
        temperature=0.1,
        verbose=True,
        time=0.0  # Set to > 0 if you want the model to use reasoning/thinking
    )
    
    print("\nResult 1 (Basic):")
    print(f"Model Used: {response.get('model_name')}")
    print(f"Cost: ${response.get('cost'):.6f}")
    print(f"Text:\n{response.get('result')}")


    print("\n--- Example 2: Structured Output using Pydantic ---")
    # Define a schema for the LLM to adhere to
    class SentimentAnalysis(BaseModel):
        sentiment: str
        confidence_score: float
        key_topics: list[str]

    structured_response = llm_invoke(
        prompt="Analyze the sentiment of this review: '{review}'",
        input_json={"review": "The new design is incredibly fast and intuitive, though the color scheme is a bit jarring."},
        strength=0.5,
        temperature=0.1,
        output_pydantic=SentimentAnalysis,
        verbose=True
    )

    print("\nResult 2 (Structured):")
    print(f"Model Used: {structured_response.get('model_name')}")
    # The result is automatically parsed into the Pydantic model instance
    result_obj = structured_response.get('result')
    if isinstance(result_obj, SentimentAnalysis):
        print(f"Sentiment: {result_obj.sentiment}")
        print(f"Confidence: {result_obj.confidence_score}")
        print(f"Topics: {', '.join(result_obj.key_topics)}")


    print("\n--- Example 3: Batch Processing ---")
    # Passing a list of dictionaries to input_json triggers batch processing
    batch_inputs = [
        {"word": "Apple"},
        {"word": "Banana"},
        {"word": "Cherry"}
    ]
    
    batch_response = llm_invoke(
        prompt="Write a one-sentence fun fact about a {word}.",
        input_json=batch_inputs,
        strength=0.0,  # 0.0 requests the cheapest available model
        temperature=0.5,
        use_batch_mode=True,
        verbose=True
    )
    
    print("\nResult 3 (Batch):")
    print(f"Model Used: {batch_response.get('model_name')}")
    results_list = batch_response.get('result', [])
    for i, res in enumerate(results_list):
        print(f"Fact {i+1}: {res}")

if __name__ == "__main__":
    main()