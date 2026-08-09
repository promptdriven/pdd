import csv
import json
from pathlib import Path
import sys

# Ensure the module can be imported (assuming it's in the same directory or python path)
# If the module is named 'token_counter.py'
try:
    import token_counter
except ImportError:
    # Fallback for demonstration if running directly where the file might be
    sys.path.append(str(Path(__file__).parent))
    import token_counter

def create_dummy_pricing_csv(path: Path):
    """Creates a temporary pricing CSV for demonstration purposes."""
    data = [
        {"model": "gpt-4", "input": "30.00"},
        {"model": "claude-3-opus", "input": "15.00"},
        {"model": "claude-sonnet-4", "input": "3.00"},
    ]
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(path, 'w', newline='') as f:
        writer = csv.DictWriter(f, fieldnames=["model", "input"])
        writer.writeheader()
        writer.writerows(data)
    print(f"Created dummy pricing file at: {path}")

def main():
    # 1. Setup: Define a sample text and a path for the pricing CSV
    sample_text = (
        "This is a sample text to demonstrate token counting. "
        "It uses the tiktoken library to estimate usage."
    )
    
    # In a real app, this would likely be ".pdd/llm_model.csv"
    pricing_path = Path(".pdd/llm_model.csv")
    
    # Create dummy data if it doesn't exist so the example runs
    if not pricing_path.exists():
        create_dummy_pricing_csv(pricing_path)

    print(f"--- Analyzing Text ({len(sample_text)} chars) ---")

    # 2. Basic Token Counting
    # Uses tiktoken (cl100k_base) to count tokens
    count = token_counter.count_tokens(sample_text)
    print(f"Token Count: {count}")

    # 3. Check Context Limits
    # Returns the limit for a specific model family
    model_name = "gpt-4-turbo"
    limit = token_counter.get_context_limit(model_name)
    print(f"Context Limit for {model_name}: {limit:,} tokens")

    # 4. Estimate Cost
    # Calculates cost based on the CSV pricing data
    # Note: Pricing is per 1,000,000 tokens
    cost_est = token_counter.estimate_cost(
        token_count=count, 
        model="gpt-4", 
        pricing_csv=pricing_path
    )
    
    if cost_est:
        print(f"Estimated Cost (GPT-4): ${cost_est.input_cost:.6f}")
    else:
        print("Could not estimate cost (missing CSV or model data).")

    # 5. Get Comprehensive Metrics
    # Returns a TokenMetrics object containing count, usage %, and cost
    print("\n--- Comprehensive Metrics (Claude Sonnet) ---")
    metrics = token_counter.get_token_metrics(
        text=sample_text,
        model="claude-sonnet-4",
        pricing_csv=pricing_path
    )

    # Convert to dictionary for easy serialization/logging
    print(json.dumps(metrics.to_dict(), indent=2))

    # 6. Show reported context limits for Claude 4 models
    print("\n--- Claude 4 Context Limits (reported) ---")
    for model in ["claude-sonnet-4-20250514", "claude-opus-4-20250514"]:
        limit = token_counter.get_context_limit(model)
        if limit is None:
            print(f"  {model}: (no context limit info available)")
        else:
            print(f"  {model}: {limit:,} tokens")

    # 7. Bedrock model name handling
    # AWS Bedrock uses prefixed names like "anthropic.claude-opus-4-6-v1"
    print("\n--- Bedrock Model Names ---")
    bedrock_model = "anthropic.claude-opus-4-6-v1"
    limit = token_counter.get_context_limit(bedrock_model)
    if limit is None:
        print(f"  {bedrock_model}: (no context limit info available)")
    else:
        print(f"  {bedrock_model}: {limit:,} tokens")

    # 8. Unknown models return None (no configured context limit)
    print("\n--- Unknown Model (no configured limit) ---")
    unknown_limit = token_counter.get_context_limit("some-custom-model-v2")
    if unknown_limit is None:
        print("  some-custom-model-v2: no configured context limit (returned None)")
    else:
        print(f"  some-custom-model-v2: {unknown_limit:,} tokens")

    # Clean up dummy file (optional)
    # pricing_path.unlink()

if __name__ == "__main__":
    main()