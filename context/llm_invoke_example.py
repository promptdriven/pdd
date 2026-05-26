import os
import sys
from typing import Dict, Any
from pdd.llm_invoke import llm_invoke

def main() -> None:
    """Example script demonstrating how to use llm_invoke."""
    # Check for a required API key to avoid interactive prompts in headless mode
    api_key = os.environ.get("OPENAI_API_KEY")
    if not api_key:
        print("OPENAI_API_KEY not set. Set it to run this example.")
        sys.exit(0)

    print("--- Basic LLM Invocation ---")
    
    # Define the prompt template and the input variables
    prompt_template = "Write a one-sentence greeting for a user named {name} from a {role}."
    input_vars = {
        "name": "Alice",
        "role": "friendly robot"
    }
    
    # Call llm_invoke with standard parameters
    # - strength (0.0 to 1.0): Determines model selection (0=cheapest, 0.5=base, 1=highest ELO)
    # - temperature: Controls randomness of the output
    # - time: Controls reasoning effort/budget (0.0 to 1.0)
    response: Dict[str, Any] = llm_invoke(
        prompt=prompt_template,
        input_json=input_vars,
        strength=0.5,
        temperature=0.7,
        time=0.25,
        verbose=True
    )
    
    # Extract and display the outputs
    print("\n--- Output Results ---")
    print(f"Result Content: {response.get('result')}")
    print(f"Model Used: {response.get('model_name')}")
    print(f"Estimated Cost: ${response.get('cost'):.6f}")
    print(f"Finish Reason: {response.get('finish_reason')}")
    print(f"Models Attempted: {response.get('attempted_models')}")

if __name__ == "__main__":
    main()