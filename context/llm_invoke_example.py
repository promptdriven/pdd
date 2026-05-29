import os
import sys
from typing import Optional
from pydantic import BaseModel

# Check for a common API key to ensure the example can run non-interactively
api_key = os.environ.get("OPENAI_API_KEY")
if not api_key:
    print("OPENAI_API_KEY not set. Set it to run this example.")
    sys.exit(0)

# Disable interactive prompts in llm_invoke (forces non-interactive mode)
os.environ["PDD_FORCE"] = "1"

# Import the functions from the module
from pdd.llm_invoke import llm_invoke, set_verbose_logging


def run_basic_example():
    print("\n--- Running Basic Text Generation ---")
    # 1. Basic Text Generation
    # llm_invoke takes a prompt template and a dictionary of inputs.
    # 'strength' determines the model selection (0.5 typically uses the base model).
    response = llm_invoke(
        prompt="Translate the following text to French: '{text}'",
        input_json={"text": "Hello world, how are you today?"},
        strength=0.5,
        temperature=0.3,
        time=0.0  # No reasoning time requested
    )
    
    print("Selected Model:", response.get("model_name"))
    print("Cost (USD):", response.get("cost"))
    print("Result:\n", response.get("result"))


def run_structured_output_example():
    print("\n--- Running Structured Output (Pydantic) ---")
    # 2. Structured Output using Pydantic
    # Define a Pydantic model for the expected JSON output.
    class SentimentAnalysis(BaseModel):
        sentiment: str
        confidence_score: float
        key_phrases: list[str]

    response = llm_invoke(
        prompt="Analyze the sentiment of this review: '{review}'. Output as JSON.",
        input_json={"review": "The product is absolutely fantastic! I use it every day and it saves me so much time. However, the packaging was a bit flimsy."},
        strength=0.8,  # Higher strength requests a more capable model
        temperature=0.1,
        output_pydantic=SentimentAnalysis
    )
    
    result_obj = response.get("result")
    print("Selected Model:", response.get("model_name"))
    if isinstance(result_obj, SentimentAnalysis):
        print("Successfully parsed Pydantic Object:")
        print(f"  Sentiment: {result_obj.sentiment}")
        print(f"  Confidence: {result_obj.confidence_score}")
        print(f"  Phrases: {result_obj.key_phrases}")
    else:
        print("Raw Result (parsing failed):\n", result_obj)


def run_batch_example():
    print("\n--- Running Batch Processing ---")
    # 3. Batch Mode
    # Pass a list of dictionaries as input_json and set use_batch_mode=True
    batch_inputs = [
        {"topic": "space exploration"},
        {"topic": "deep sea diving"},
        {"topic": "artificial intelligence"}
    ]
    
    response = llm_invoke(
        prompt="Give me a one-sentence fun fact about {topic}.",
        input_json=batch_inputs,
        strength=0.3,  # Lower strength requests a cheaper/faster model
        use_batch_mode=True,
        temperature=0.5
    )
    
    print("Selected Model:", response.get("model_name"))
    results = response.get("result", [])
    for i, res in enumerate(results):
        print(f"Fact {i+1}: {res}")


if __name__ == "__main__":
    # Optional: Enable verbose logging to see LiteLLM debug info and model selection details
    set_verbose_logging(False)
    
    run_basic_example()
    run_structured_output_example()
    run_batch_example()