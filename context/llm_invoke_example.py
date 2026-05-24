import os
import sys
from typing import Optional, Dict, Any
from pydantic import BaseModel

try:
    # Import the target function and logging utility from the module
    from pdd.llm_invoke import llm_invoke, set_verbose_logging
except ImportError:
    # Mock for graceful degradation if module is not present in environment
    def llm_invoke(*args, **kwargs) -> Dict[str, Any]:
        return {"result": None, "model_name": "mock_model", "cost": 0.0}
    def set_verbose_logging(*args, **kwargs) -> None:
        pass

class Joke(BaseModel):
    """Pydantic model to enforce the structure of the LLM's response."""
    setup: str
    punchline: str
    rating: int

def main() -> None:
    """Main execution function demonstrating basic and structured LLM invocations."""
    # Ensure output directory exists if we needed to write files
    os.makedirs("./output", exist_ok=True)

    # We check for a common API key to ensure the example can run non-interactively.
    # llm_invoke supports many providers, but we check OPENAI_API_KEY here as a baseline.
    api_key: Optional[str] = os.environ.get("OPENAI_API_KEY")
    if not api_key:
        print("OPENAI_API_KEY not set. Set it to run this example.")
        sys.exit(0)

    # Enable verbose logging to see the internal model selection and token usage details
    set_verbose_logging(verbose=True)

    print("\n--- Example 1: Basic Text Generation ---")
    # llm_invoke takes a prompt template and a dictionary of inputs to format it.
    # strength=0.5 selects the base model defined in your llm_model.csv or environment.
    basic_response: Dict[str, Any] = llm_invoke(
        prompt="Explain what a {topic} is in one short sentence.",
        input_json={"topic": "variable"},
        strength=0.5, 
        temperature=0.3,
        verbose=True
    )

    print("\nResult:")
    print(basic_response.get("result", "No result"))
    print(f"Model Used: {basic_response.get('model_name', 'Unknown')}")
    print(f"Estimated Cost: ${basic_response.get('cost', 0.0):.6f}")

    print("\n--- Example 2: Structured Output using Pydantic ---")
    # By passing output_pydantic, llm_invoke ensures the response is parsed into this model.
    structured_response: Dict[str, Any] = llm_invoke(
        prompt="Tell me a developer joke about {topic}.",
        input_json={"topic": "recursion"},
        strength=0.5,
        temperature=0.7,
        output_pydantic=Joke,
        verbose=True
    )

    print("\nStructured Result (Parsed Object):")
    # The result is automatically validated and returned as the Pydantic model instance
    joke_obj = structured_response.get("result")
    if isinstance(joke_obj, Joke):
        print(f"Setup: {joke_obj.setup}")
        print(f"Punchline: {joke_obj.punchline}")
        print(f"Rating: {joke_obj.rating}/10")
    else:
        print("Failed to parse structured output properly.")
        
    print(f"Model Used: {structured_response.get('model_name', 'Unknown')}")
    print(f"Estimated Cost: ${structured_response.get('cost', 0.0):.6f}")

if __name__ == "__main__":
    main()